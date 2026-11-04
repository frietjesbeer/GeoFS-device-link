// ==UserScript==
// @name         GeoFS Companion
// @namespace    geofs-companion
// @version      0.4.0
// @description  Streams GeoFS flight data over WebRTC (PeerJS) to a phone PWA and lets it control the autopilot, direct-to and pause remotely
// @match        https://www.geo-fs.com/geofs.php*
// @match        https://geo-fs.com/geofs.php*
// @match        https://beta.geo-fs.com/geofs.php?v=4
// @grant        unsafeWindow
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_registerMenuCommand
// @connect      0.peerjs.com
// @require      https://cdn.jsdelivr.net/npm/peerjs@1.5.4/dist/peerjs.min.js
// @require      https://cdn.jsdelivr.net/npm/qrcode-generator@1.4.4/qrcode.js
// @run-at       document-idle
// ==/UserScript==
(function () {
  'use strict';

  // ===== CONFIG =====
  const CONFIG = {
    PWA_URL: 'https://frietjesbeer.github.io/GeoFS-device-link/', // with trailing slash
    RATE_HZ: 8,          // state messages per second
    CMD_PER_SEC: 8,      // max. commands per second from the phone
    IAS_TAU: 1.5,       // time constant (s) of the IAS filter: higher = calmer but slower
    // Own TURN/PeerJS server later: add iceServers or host/port/path here.
    PEER_OPTIONS: { config: { iceServers: [{ urls: 'stun:stun.l.google.com:19302' } /*, {urls:'turn:host:3478',username:'',credential:''} */] } },
  };

  // ===== MATH HELPERS (pure, no GeoFS) =====
  const D2R = Math.PI / 180;
  const wrap180 = (a) => ((((a % 360) + 540) % 360) - 180);
  const bearing = (la1, lo1, la2, lo2) => {
    const p1 = la1 * D2R, p2 = la2 * D2R, dl = (lo2 - lo1) * D2R;
    const y = Math.sin(dl) * Math.cos(p2), x = Math.cos(p1) * Math.sin(p2) - Math.sin(p1) * Math.cos(p2) * Math.cos(dl);
    return ((Math.atan2(y, x) / D2R) + 360) % 360;
  };
  const distNm = (la1, lo1, la2, lo2) => {
    const p1 = la1 * D2R, p2 = la2 * D2R, dp = p2 - p1, dl = (lo2 - lo1) * D2R;
    const a = Math.sin(dp / 2) ** 2 + Math.cos(p1) * Math.cos(p2) * Math.sin(dl / 2) ** 2;
    return 3440.065 * 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
  };
  // Mach from IAS and altitude (ISA, QNH 1013 assumed). Only used when GeoFS provides no animation.values.mach itself.
  const machFrom = (ias, altFt) => {
    const qcp0 = Math.pow(1 + 0.2 * (ias / 661.4788) ** 2, 3.5) - 1;
    const delta = altFt < 36089 ? Math.pow(1 - 6.8755856e-6 * altFt, 5.2558797) : 0.2233 * Math.exp(-(altFt - 36089) / 20806.7);
    const m2 = 5 * (Math.pow(qcp0 / delta + 1, 2 / 7) - 1);
    return m2 > 0 ? Math.sqrt(m2) : 0;
  };

  // ===== ADAPTER: ALL GeoFS-specific code lives here =====
  // Confirmed (diagnostics + public addons): geofs.aircraft.instance.llaLocation [lat, lon, m];
  //   geofs.animation.values: altitude (ft), kias, groundSpeedKnt, heading360, atilt, aroll, verticalSpeed (ft/min), mach, haglFeet;
  //   geofs.autopilot: on, mode, speedMode, values {course, altitude, speed, verticalSpeed}, turnOn/turnOff/setCourse/setAltitude/setSpeed/setVerticalSpeed/setMode
  //   geofs.nav.selectNavaid exists. Flight plan waypoints have ident/lat/lon/alt (per the GeoFS documentation).
  // NOT confirmed (read tolerantly, run Diagnose): geofs.flightPlan.waypointArray, geofs.nav.units.NAV1.navaid, pause function.
  const Adapter = (() => {
    const W = unsafeWindow, FT = 3.28084;
    // +pitch = nose up, +roll = right wing down. GeoFS aroll is mirrored, hence -1.
    const SIGN = { pitch: 1, roll: -1 };
    const num = (x, name) => { if (typeof x !== 'number' || !isFinite(x)) throw new Error('GeoFS variable missing/invalid: ' + name); return x; };
    const r = (x, d = 1) => Math.round(x * 10 ** d) / 10 ** d;
    const optNum = (x, d = 0) => { const n = typeof x === 'number' ? x : parseFloat(x); return isFinite(n) ? r(n, d) : null; }; // AP values are sometimes strings
    const str = (x, n = 12) => (typeof x === 'string' || typeof x === 'number' ? String(x).slice(0, n) : null);
    const first = (...xs) => { for (const x of xs) { const n = typeof x === 'number' ? x : parseFloat(x); if (isFinite(n)) return n; } return NaN; };

    // IAS filter: exponential smoothing (time constant CONFIG.IAS_TAU) with clamped spikes. A single outlier pulls the value
    // by at most 15 kt * (dt/tau); a real acceleration (or a >50 kt difference: new aircraft, teleport) is simply followed.
    // (Earlier: median of 5. That gets stuck in runs when the input jumps back and forth and made the output swing along.)
    let iasF = null, iasT = 0;
    function filterIas(x) {
      const now = Date.now(), dt = (now - iasT) / 1000;
      if (iasF === null || dt > 2 || Math.abs(x - iasF) > 50) iasF = x;
      else iasF += (Math.max(iasF - 15, Math.min(iasF + 15, x)) - iasF) * (1 - Math.exp(-dt / CONFIG.IAS_TAU));
      iasT = now; return iasF;
    }

    function autopilot() { const a = W.geofs && W.geofs.autopilot; if (!a) throw new Error('geofs.autopilot not available'); return a; }
    function call(name, ...args) {
      const a = autopilot();
      if (typeof a[name] !== 'function') throw new Error('geofs.autopilot.' + name + ' is missing (GeoFS update?)');
      return a[name](...args);
    }

    function readState() {
      const g = W.geofs;
      if (!g || !g.aircraft || !g.aircraft.instance) throw new Error('geofs.aircraft.instance not available (aircraft not loaded yet?)');
      const inst = g.aircraft.instance, v = g.animation && g.animation.values;
      if (!v) throw new Error('geofs.animation.values not available');
      const lla = inst.llaLocation;
      if (!lla) throw new Error('geofs.aircraft.instance.llaLocation is missing');
      const alt = typeof v.altitude === 'number' ? v.altitude : num(lla[2], 'llaLocation[2]') * FT;
      const ias = filterIas(num(v.kias, 'animation.values.kias'));
      const mach = typeof v.mach === 'number' && v.mach > 0 ? v.mach : ias > 30 ? machFrom(ias, alt) : 0;
      const ap = g.autopilot, av = (ap && ap.values) || {};
      return {
        lat: r(num(lla[0], 'llaLocation[0]'), 6), lon: r(num(lla[1], 'llaLocation[1]'), 6), alt: r(alt, 0),
        ias: r(ias), mach: r(mach, 3),
        gs: r(num(v.groundSpeedKnt ?? v.groundSpeed, 'animation.values.groundSpeedKnt')),
        hdg: r(num(v.heading360 ?? v.heading, 'animation.values.heading360')),
        pitch: r(SIGN.pitch * num(v.atilt, 'animation.values.atilt'), 2),
        roll: r(SIGN.roll * num(v.aroll, 'animation.values.aroll'), 2),
        vs: r(num(v.verticalSpeed, 'animation.values.verticalSpeed'), 0),
        hagl: optNum(v.haglFeet) ?? optNum(typeof v.groundElevationFeet === 'number' ? alt - v.groundElevationFeet : null),
        paused: isPaused(),
        ap: { on: !!(ap && ap.on), hdg: optNum(av.course), alt: optNum(av.altitude), spd: optNum(av.speed), vs: optNum(av.verticalSpeed), mode: ap ? str(ap.mode) : null, spdMode: ap ? str(ap.speedMode) : null },
      };
    }

    // --- radio: the navaid tuned in GeoFS (NAV1) ---
    function navaid() {
      const n = W.geofs && W.geofs.nav; if (!n) return null;
      const u = n.units && (n.units.NAV1 || n.units.nav1 || Object.values(n.units)[0]);
      const na = (u && u.navaid) || n.selectedNavaid || null;
      if (!na || typeof na !== 'object') return null;
      const lat = first(na.lat, na.lla && na.lla[0], na.location && na.location[0], na.coords && na.coords[0]);
      const lon = first(na.lon, na.lla && na.lla[1], na.location && na.location[1], na.coords && na.coords[1]);
      if (!isFinite(lat) || !isFinite(lon)) return null;
      return { ident: str(na.ident ?? na.id ?? na.name ?? na.code, 8), type: str(na.type, 8), freq: first(na.freq, na.frequency), lat, lon, hdg: first(na.heading, na.hdg, na.course, na.crs), slope: first(na.slope, na.glideslope, na.gs) };
    }

    // --- GeoFS flight plan (NAV panel) ---
    function flightPlan() {
      const fp = W.geofs && W.geofs.flightPlan; if (!fp) return null;
      const arr = fp.waypointArray || fp.waypoints || fp.route; if (!Array.isArray(arr)) return null;
      const out = [];
      arr.forEach((w, i) => {
        if (!w || typeof w !== 'object') return;
        const lat = first(w.lat, w.lla && w.lla[0]), lon = first(w.lon, w.lla && w.lla[1]);
        if (!isFinite(lat) || !isFinite(lon)) return;
        out.push({ n: str(w.ident ?? w.id ?? w.name, 8) || 'WP' + (i + 1), lat: r(lat, 5), lon: r(lon, 5), alt: isFinite(parseFloat(w.alt)) ? Math.round(parseFloat(w.alt)) : null });
      });
      return out.slice(0, 80);
    }

    // --- pause ---
    function isPaused() {
      const g = W.geofs; if (!g) return null;
      try {
        if (typeof g.isPaused === 'function') return !!g.isPaused();
        if (typeof g.isPaused === 'boolean') return g.isPaused;
        if (typeof g.paused === 'boolean') return g.paused;
      } catch (e) { /* ignore */ }
      return null;
    }
    function setPaused(on) {
      const g = W.geofs; if (!g) throw new Error('geofs not available');
      const cur = isPaused(); if (cur === on) return;
      if (typeof g.togglePause === 'function') { g.togglePause(); return; }
      if (on && typeof g.pause === 'function') { g.pause(); return; }
      if (!on && typeof g.unpause === 'function') { g.unpause(); return; }
      throw new Error('no pause function found in GeoFS (see Diagnose)');
    }

    // --- autopilot setters (units: degrees, feet, knots IAS, feet/min) ---
    function apOn() { return !!autopilot().on; }
    function setAutopilot(on) { call(on ? 'turnOn' : 'turnOff'); }
    function setHeading(deg) { call('setCourse', deg); }
    function setAltitude(ft) { call('setAltitude', ft); }
    function setSpeed(kt) {
      const a = autopilot();
      // In Mach mode GeoFS expects a Mach number: a knots value would send the aircraft into an extreme acceleration.
      if (/mach/i.test(String(a.speedMode))) throw new Error('GeoFS is in Mach mode: set the speed to IAS (knots) in GeoFS');
      call('setSpeed', kt);
    }
    function setVS(fpm) { call('setVerticalSpeed', fpm); }
    function ensureHdgMode() { const a = autopilot(); if (a.mode && String(a.mode).toUpperCase() !== 'HDG' && typeof a.setMode === 'function') a.setMode('HDG'); }
    return { readState, navaid, flightPlan, isPaused, setPaused, apOn, setAutopilot, setHeading, setAltitude, setSpeed, setVS, ensureHdgMode };
  })();

  // ===== NAV: info about the tuned navaid + own direct-to (runs here, so it keeps going if the phone drops) =====
  const Nav = (() => {
    const r = (x, d = 1) => Math.round(x * 10 ** d) / 10 ** d;
    // Bearing/distance to the tuned navaid. For an ILS also localizer and glideslope deviation, computed here from
    // position and ILS course (GeoFS's own values are not verified). loc: degrees off the course line (+ = fly right),
    // gs: degrees relative to 3° (negative = below the glideslope).
    function info(s) {
      const na = Adapter.navaid(); if (!na) return null;
      const out = { id: na.ident, type: na.type, freq: isFinite(na.freq) ? na.freq : null, brg: r(bearing(s.lat, s.lon, na.lat, na.lon), 0), dist: r(distNm(s.lat, s.lon, na.lat, na.lon), 1), crs: null, loc: null, gs: null };
      if (/ils|loc/i.test(na.type || '') && isFinite(na.hdg)) {
        out.crs = r(na.hdg, 0);
        const loc = wrap180(bearing(na.lat, na.lon, s.lat, s.lon) - (na.hdg + 180));
        if (Math.abs(loc) <= 30) {
          out.loc = r(loc, 2);
          if (s.hagl != null && out.dist > 0.3) out.gs = r(Math.atan2(s.hagl, out.dist * 6076.12) / D2R - (isFinite(na.slope) && na.slope > 0 && na.slope < 10 ? na.slope : 3), 2);
        }
      }
      return out;
    }

    let on = false, idx = 0, plan = [], lastCmd = null, brg = 0, dist = 0, done = false;
    function start(i) {
      const p = Adapter.flightPlan();
      if (!p || !p.length) throw new Error('no flight plan found in GeoFS');
      if (!Number.isInteger(i) || i < 0 || i >= p.length) throw new Error('waypoint ' + i + ' does not exist');
      plan = p; idx = i; on = true; done = false; lastCmd = null;
      Adapter.ensureHdgMode();
    }
    function cancel() { on = false; done = false; }
    // Once per second: steers the AP heading to the active waypoint and advances to the next one.
    function tick(s) {
      if (!on) return;
      try {
        let w = plan[idx], d = distNm(s.lat, s.lon, w.lat, w.lon);
        const cap = Math.min(3, Math.max(0.8, s.gs / 150)); // rough turn anticipation (nm)
        if (d < cap) {
          if (idx + 1 < plan.length) { idx++; w = plan[idx]; d = distNm(s.lat, s.lon, w.lat, w.lon); lastCmd = null; }
          else { on = false; done = true; return; }
        }
        brg = bearing(s.lat, s.lon, w.lat, w.lon); dist = d;
        const target = Math.round(brg) % 360;
        if (lastCmd === null || Math.abs(wrap180(target - lastCmd)) >= 1) { Adapter.setHeading(target); lastCmd = target; }
      } catch (e) { on = false; console.warn('[GeoFS Companion] direct-to stopped:', e.message); }
    }
    const status = () => (on ? { on: true, idx, n: plan[idx] && plan[idx].n, brg: r(brg, 0), dist: r(dist, 1) } : { on: false, done });
    return { info, start, cancel, tick, status };
  })();

  // ===== COMMANDS: validation + clamping, only then passed to the adapter =====
  const Commands = (() => {
    const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));
    const num = (v, name) => { if (typeof v !== 'number' || !isFinite(v)) throw new Error(name + ': number expected'); return v; };
    const DEFS = {
      ap_toggle: (v) => {
        if (v != null && typeof v !== 'boolean') throw new Error('value must be true/false');
        const on = v == null ? !Adapter.apOn() : v;
        Adapter.setAutopilot(on); return on;
      },
      set_hdg: (v) => { const x = ((Math.round(num(v, 'hdg')) % 360) + 360) % 360; Nav.cancel(); Adapter.setHeading(x); return x; }, // a manual heading cancels direct-to
      set_alt: (v) => { const x = clamp(Math.round(num(v, 'alt')), 0, 60000); Adapter.setAltitude(x); return x; },
      set_spd: (v) => { const x = clamp(Math.round(num(v, 'spd')), 60, 700); Adapter.setSpeed(x); return x; },
      set_vs: (v) => { const x = clamp(Math.round(num(v, 'vs')), -6000, 6000); Adapter.setVS(x); return x; },
      sim_pause: (v) => {
        if (v != null && typeof v !== 'boolean') throw new Error('value must be true/false');
        const want = v == null ? !Adapter.isPaused() : v; Adapter.setPaused(want); return want;
      },
      nav_direct: (v) => { Nav.start(num(v, 'waypoint')); return v; },
      nav_cancel: () => { Nav.cancel(); return true; },
    };
    let win = 0, cnt = 0;
    // Always returns an ack message; never throws.
    function run(m) {
      const id = typeof m.id === 'number' || (typeof m.id === 'string' && m.id.length <= 32) ? m.id : null;
      const now = Date.now(); if (now - win > 1000) { win = now; cnt = 0; }
      if (++cnt > CONFIG.CMD_PER_SEC) return { t: 'ack', id, ok: false, err: 'too many commands per second' };
      try {
        if (typeof m.name !== 'string' || !Object.prototype.hasOwnProperty.call(DEFS, m.name)) throw new Error('unknown command');
        const applied = DEFS[m.name](m.value);
        return { t: 'ack', id, ok: true, applied }; // applied = the (clamped) value that went to GeoFS
      } catch (e) {
        const err = String((e && e.message) || e).slice(0, 140);
        console.warn('[GeoFS Companion] command failed:', m.name, err);
        return { t: 'ack', id, ok: false, err };
      }
    }
    return { run };
  })();

  // ===== HOST (PeerJS, behind a simple interface: start/send/reset/onStatus) =====
  const Host = (() => {
    const rnd = (n) => { const a = new Uint8Array(n); crypto.getRandomValues(a); return [...a].map((b) => b.toString(16).padStart(2, '0')).join(''); };
    const newPairing = () => { const p = { id: 'gfs-' + rnd(12), token: rnd(16) }; GM_setValue('peerId', p.id); GM_setValue('token', p.token); GM_setValue('trusted', '[]'); return p; };
    let pairing = { id: GM_getValue('peerId'), token: GM_getValue('token') };
    if (!pairing.id || !pairing.token) pairing = newPairing();
    let peer = null, conn = null, attempt = 0, timer = null, statusCb = () => {}, winStart = 0, cnt = 0, epoch = 0;

    const send = (m) => {
      try { if (conn && conn.open && !(conn.dataChannel && conn.dataChannel.bufferedAmount > 65536)) conn.send(m); } catch (e) { /* ignore */ }
    };
    const retry = (fn) => { if (timer) return; const d = Math.min(30000, 1000 * 2 ** attempt++); statusCb('reconnecting to broker…'); timer = setTimeout(() => { timer = null; fn(); }, d); };

    function handle(m) {
      const now = Date.now(); if (now - winStart > 1000) { winStart = now; cnt = 0; }
      if (++cnt > 30 || !m || typeof m !== 'object') return; // general rate limit
      if (m.t === 'ping') return; // liveness = any message
      if (m.t === 'cmd') send(Commands.run(m));
    }
    function onConn(c) {
      let authed = false;
      const to = setTimeout(() => { if (!authed) c.close(); }, 5000);
      c.on('data', (m) => {
        if (!authed) {
          if (!m || m.t !== 'hello' || m.token !== pairing.token || typeof m.dev !== 'string') { c.close(); return; }
          const trusted = JSON.parse(GM_getValue('trusted', '[]'));
          if (!trusted.includes(m.dev)) {
            if (!confirm('GeoFS Companion: a new phone wants to pair. Allow?')) { c.close(); return; }
            trusted.push(m.dev); GM_setValue('trusted', JSON.stringify(trusted));
          }
          authed = true; clearTimeout(to);
          if (conn && conn !== c) { try { conn.close(); } catch (e) { /* ignore */ } } // one phone at a time
          conn = c; epoch++; c.send({ t: 'hello_ok', v: 1 }); statusCb('phone connected'); return;
        }
        if (c === conn) handle(m);
      });
      c.on('close', () => { clearTimeout(to); if (conn === c) { conn = null; statusCb('waiting for phone'); } });
      c.on('error', () => {});
    }
    function start() {
      try { if (peer) peer.destroy(); } catch (e) { /* ignore */ }
      const p = (peer = new Peer(pairing.id, CONFIG.PEER_OPTIONS));
      p.on('open', () => { attempt = 0; statusCb('waiting for phone'); });
      p.on('connection', onConn);
      p.on('disconnected', () => { if (peer === p) retry(() => p.reconnect()); }); // the P2P connection keeps working meanwhile
      p.on('error', (e) => {
        console.warn('[GeoFS Companion] peer error', e.type);
        if (peer === p && ['unavailable-id', 'network', 'server-error', 'socket-error', 'socket-closed'].includes(e.type)) retry(start);
      });
      p.on('close', () => { if (peer === p) retry(start); });
    }
    return {
      start, send,
      get pairing() { return pairing; },
      get connected() { return !!(conn && conn.open); },
      get epoch() { return epoch; }, // increments on every (re)pairing: after that we resend the flight plan
      onStatus: (cb) => { statusCb = cb; },
      reset() { try { if (conn) conn.close(); } catch (e) { /* ignore */ } conn = null; pairing = newPairing(); attempt = 0; start(); },
    };
  })();

  // ===== DIAGNOSE (output in the browser console, F12) =====
  function diagnose() {
    const g = unsafeWindow.geofs;
    if (!g) { UI.note('geofs not found'); return; }
    // Depth-limited dump so large GeoFS objects don't flood the console
    const dump = (o, d = 0) => {
      if (o === null || typeof o !== 'object') return typeof o === 'function' ? '[fn]' : o;
      if (d >= 3) return Array.isArray(o) ? '[array ' + o.length + ']' : '[object]';
      if (Array.isArray(o)) return o.slice(0, 5).map((x) => dump(x, d + 1));
      const out = {}; Object.keys(o).slice(0, 40).forEach((k) => { let v; try { v = o[k]; } catch (e) { v = '[err]'; } out[k] = dump(v, d + 1); }); return out;
    };
    const show = (label, o) => { try { console.log(label, JSON.stringify(dump(o))); } catch (e) { console.log(label, '[cannot be shown]'); } };
    const v = g.animation && g.animation.values, inst = g.aircraft && g.aircraft.instance, ap = g.autopilot;
    console.log('[Companion diagnostics] aircraft.instance:', !!inst, '| animation.values:', !!v, '| autopilot:', !!ap);
    if (inst) console.log('llaLocation [lat, lon, alt m]:', inst.llaLocation);
    if (v) {
      const keys = ['altitude', 'kias', 'mach', 'haglFeet', 'groundElevationFeet', 'groundSpeedKnt', 'heading360', 'pitch', 'roll', 'atilt', 'aroll', 'apitch', 'verticalSpeed'];
      console.table(keys.map((k) => ({ key: k, value: v[k], type: typeof v[k] })));
      console.log('Keys with nav/ils/loc/glide/dme:', Object.keys(v).filter((k) => /nav|ils|loc|glide|slope|dme|course|dev/i.test(k)));
    }
    if (ap) {
      console.log('autopilot: on=' + ap.on, 'mode=' + ap.mode, 'speedMode=' + ap.speedMode, 'values=' + JSON.stringify(ap.values));
      ['turnOn', 'turnOff', 'setCourse', 'setAltitude', 'setSpeed', 'setVerticalSpeed', 'setMode'].forEach((k) => console.log('autopilot.' + k + ' =', typeof ap[k] === 'function' ? String(ap[k]) : '(missing)'));
    }
    // Radio / navaid / flight plan / pause: send these lines to Claude if something doesn't work
    console.log('geofs keys with pause:', Object.keys(g).filter((k) => /pause/i.test(k)), '| isPaused():', (() => { try { return typeof g.isPaused === 'function' ? g.isPaused() : g.isPaused; } catch (e) { return '[err]'; } })());
    if (g.nav) {
      console.log('geofs.nav keys:', Object.keys(g.nav));
      if (g.nav.units) { console.log('geofs.nav.units keys:', Object.keys(g.nav.units)); Object.keys(g.nav.units).slice(0, 3).forEach((k) => show('geofs.nav.units.' + k + ' =', g.nav.units[k])); }
      show('Adapter.navaid() =', Adapter.navaid());
    } else console.log('geofs.nav is missing');
    if (g.flightPlan) { console.log('geofs.flightPlan keys:', Object.keys(g.flightPlan)); show('Adapter.flightPlan() =', Adapter.flightPlan()); show('first waypoint raw =', (g.flightPlan.waypointArray || [])[0]); }
    else console.log('geofs.flightPlan is missing');
    // Measure for 12 seconds. Bank RIGHT and pull the nose UP; the hints say which sign is correct.
    let n = 0, lastH = null;
    const t = setInterval(() => {
      if (!v) { clearInterval(t); return; }
      const h = v.heading360 ?? v.heading, hdgRate = lastH === null ? 0 : ((h - lastH + 540) % 360) - 180; lastH = h;
      const gamma = Math.atan2(v.verticalSpeed / 60, (v.groundSpeedKnt ?? v.groundSpeed) * 1.68781) * 180 / Math.PI;
      console.log(`#${++n} pitch=${v.pitch} atilt=${v.atilt} | roll=${v.roll} aroll=${v.aroll} | hdgRate=${hdgRate.toFixed(1)}°/s | vs=${v.verticalSpeed} pathAngle=${gamma.toFixed(1)}° | mach=${v.mach}`);
      if (Math.abs(v.aroll) > 8 && Math.abs(hdgRate) > 0.5) console.log('   HINT roll: aroll ' + (v.aroll * hdgRate > 0 ? 'positive = turn to the RIGHT (SIGN.roll = 1)' : 'positive = turn to the LEFT (SIGN.roll = -1)'));
      if (Math.abs(v.aroll) < 10) console.log(`   HINT pitch: atilt-pathAngle=${(v.atilt - gamma).toFixed(1)}° | -atilt-pathAngle=${(-v.atilt - gamma).toFixed(1)}° (in straight flight the correct one should be between 0° and ~8°)`);
      if (n >= 12) clearInterval(t);
    }, 1000);
    UI.note('Diagnostics running for 12 s, see the console (F12)');
  }

  // ===== PWA (embedded as a single file: index.html with inline CSS/JS/manifest/icon) =====
  const PWA_HTML = "<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width,initial-scale=1,viewport-fit=cover,user-scalable=no\">\n<meta name=\"theme-color\" content=\"#0d1015\">\n<meta name=\"apple-mobile-web-app-capable\" content=\"yes\"><meta name=\"mobile-web-app-capable\" content=\"yes\">\n<meta name=\"apple-mobile-web-app-status-bar-style\" content=\"black-translucent\">\n<link rel=\"manifest\" href=\"data:application/manifest+json,%7B%22name%22%3A%20%22GeoFS%20Companion%22%2C%20%22short_name%22%3A%20%22GeoFS%22%2C%20%22start_url%22%3A%20%22.%22%2C%20%22scope%22%3A%20%22.%22%2C%20%22display%22%3A%20%22standalone%22%2C%20%22orientation%22%3A%20%22any%22%2C%20%22background_color%22%3A%20%22%230a0e14%22%2C%20%22theme_color%22%3A%20%22%230a0e14%22%2C%20%22icons%22%3A%20%5B%7B%22src%22%3A%20%22data%3Aimage/png%3Bbase64%2CiVBORw0KGgoAAAANSUhEUgAAAMAAAADACAIAAADdvvtQAAAHkElEQVR4nO2dTW7bSBCFW4NZycAABuxD%2BAq%2BP3wFHcIBsoq3mkUPCA5JUWTX36vu960Sw4nIrk%2BviiJFXq7/vBVCWvkregNIbigQEUGBiAgKRERQICKCAhERFIiIoEBEBAUiIigQEUGBiAgKRERQICKCAhERf0dvAAQ/t%2B%2BGf3X9eFffknRcBrweqE2XIwyo1BAC2Rmzzwg%2B9SxQlDdrOjapN4E8pxlOTqUngY6X066ECNvgTHqBjtQsqlrI26ZFYoGelgenNok29SwpBdqvB3Ix8m75I5IJtFMAo9X/8/Xr5VN/ifx3xIg0n0R3s%2BKVus2bO1V/mGWnciTQI3usV/nP16/6B4sQmojaOxXQEyj14h7kURqliCJcgUZQZ05SjUAv59i05/rxDruOWjzaR5zTMgsQZ6D1YoV4Mw1AFdMxaBOQddgHK4F%2Bbt8pVs2H9Y5vrk8sQAJtqjOsPZXNFYByCEUgtOBZ9K/Nn7iB7FC8QGxbR4BtZ8ECsW0dB7OdRQrE4GkAzaEwgZDteTTuBI5Bc6AcihEI2Z4U4DgUINBiVzn0tLFetxCHvAVa2%2BO8AU/Z71MgXWwi3CFXgfDtyUisQ34C0R47Ah1yEoj2WBPlUPwn0VAcGXHQxqBYPARi/PgQEkLmAtEeT/wdshUolz3HexNyF3N2yG8GArenJzyX2lCg8BPFpGJaCCuBcjWv/nBrZCYCZbTn7FiDPAZVfBwyn4FS2NMrDouvLxBHH1gsSmObQFnip60f4XexYl8CZYHmjmexp3vmhVAPIU2B2LxSoFsmqxbG%2BIHCrhxqAuWNH8kok2IMWqNYLJMEYvwAYlQUHYHyxs%2BwaJVMP4FyxY%2B8ByXqYhalURCI8ZMUlcIpJ1Cu%2BBkQ9QJJBWL8pEZePs0EShc/WuNLojGoaJeJ38ogIkQC8cxXUhTPjo2bQLp9J1cXU6RdII7P3SAppU4CsX%2BlQ6tk47YwosKgAlmMLGOOQY0C8firA1SOxQZNIKLFiALZ9ZoBu1iLQOxf3SDvYiMmEFGEAhERwwlkPaaMNgYNJxDR5fQjL/NO0M7Z4P%2BIzGYkNR0lgfw7yyC9DPex31oEFrK%2BdKIoaqBngUAyoG%2BN%2BhQIRJ05vWrU4QwEaM8E8ra1ce4oDPwQLFF50KKoubKdtLBE6lS66WjpBUqnzpwONMo9A6W2ZyL1XmRNoNSLviZvFOUTqDN15mTUKJNAHaszJ5dGaWagQeyZyLK/CRIoy1KqkyKKoAUaVp054BqBCkR1FsBqhDgD0Z5HAK4MVgIBLhAaaFGEIhDVOQWORvECUZ1mEDQKnoFoj5zYNQxLIKqjSGAUBQhEdYwI0cj1e2FUx41TGuX4Xhjt8cRttT1aGNUJwaej2QpEdcKx1shKIKoDhZ1GJjMQ7cHEoi6nj8LK7tBOdVIwjyLhd/3UWhjVSYRiR4s/F%2BbDtFgOonu%2BVjidCxR7onEEkzoUCOEihwXzTepMphaBrh/v0%2BT1c/sGucsCoDebQMWS/G4ZuRMoizSb9BFLKQVK7c0mULF0ikaB/LtYf9Js4hlLKnd7Qk%2BgQbzZJEUsIQo0sjSbIE9LOgL93L7L74vwP6E3R0CLpXaB5mNQM5SmGcVYkoywMS2M3ugSGEsigU6FEKVxoCGWhEfQ5glEb6LwiSUTgSgNFKYHcdIrEucBeHm9v3y%2B0R5kXj7fLq/3y%2Bu9/lX%2BCbDaJa11m%2BTHZcSUqUCTQ0IUBAI5G0/OolI4/YvqGUKwWJRGRyCGUDq0SmbytR6GECBGRVETiCGUCMViWd1cgSEEhV05NAViCKVAt0zKCTTfOIYQCKbPmbS9PxAdCse6BPoCsZHBYlEa8zuUMYQCcVh8E4EWptOhEBbLbtQZrBKIDsXiY08xbWEchkAwLYTfXVoZQm54LrWtQGxk/rg1r4p5AtEhT5ztKT4tjA754G9PCX9aD8mOk0AMIWtC4qd4JhAdsiPKnuLcwuiQBYH2FP8ZiA7pEmtPabtTvZy1Nz577nbvAYdvV0at4YIYgYr7/ofcTcdOIxB7SuBh/HqH7dpZ1L2YjF4Xx54S%2BzmQj0Oxd/JSf3Uoe0pgC5vYlEZlUUBuAleRtzO7hZIQL1BF/Y0FZU9F4hBa8EygnMrQbWeA9hTBVsHaU3ASqCJPaUx1FhyPIsy2NQdLoErzGy6FPZUjDiEHzwSiQKXpnZfInsqOQ/jBMwEqUHk8A63XMZ06cxYaHd9rEHAFqjxd0NT2VKpD6dSpoAtU2VlcI4E2%2B4vRaz26XSG4OpUcApXHDt3Fz%2BiYOPU5jaJMmwKlsKckEqiy1kgokMr5TqFMC4GyqFNJJlBlrlGDQKbXWjTIpHjXZn9SClSpGh0UKOT25wdlurzeM6pTQXzg3EH%2BW/Svh78Q/s6e96Yd0fPaU1ILtMnmQOp23efO%2BbuDMqWjB4H%2B155uz39f6xRB2%2Bne68f7S8F9hOVZEs9AT8G5Yj91k9qnZ4Emokzq2JuJIQRaYOfTCMYsGFGgNc3TjPqWpIMCEREol7SSpFAgIoICEREUiIigQEQEBSIiKBARQYGICApERFAgIoICEREUiIigQEQEBSIi/gXjvL0hhAdSWQAAAABJRU5ErkJggg%3D%3D%22%2C%20%22sizes%22%3A%20%22192x192%22%2C%20%22type%22%3A%20%22image/png%22%7D%2C%20%7B%22src%22%3A%20%22data%3Aimage/png%3Bbase64%2CiVBORw0KGgoAAAANSUhEUgAAAgAAAAIACAIAAAB7GkOtAAAWk0lEQVR4nO3dSY4cRxIF0KSgFQkIEEAeglfg/aEr8BAU0Ctxy16kUCoWc4jBI9yG99CL7k11MjP8/zCLGt69/%2BPjBYB%2Bfpv9AgCYQwEANKUAAJpSAABNKQCAphQAQFMKAKApBQDQlAIAaEoBADSlAACaUgAATSkAgKYUAEBTCgCgKQUA0JQCAGhKAQA0pQAAmlIAAE0pAICmFABAUwoAoCkFANCUAgBoSgEANKUAAJpSAABNKQCAphQAQFMKAKApBQDQlAIAaEoBADSlAACaUgAATSkAgKYUAEBTCgCgqd9nvwAY7PvXbwd95fefPx30lWGKd%2B//%2BDj7NcA6x0X8HuqBdBQAccUM%2BrUUA2EpAKKoEfdLqASCUABM0yfxH9MHzKIAOJXQf0wZcCYFwLEk/h76gEMpAA4h98fSBBxBATCM0D%2BHMmAUBcBecn8WTcBOCoCN5H4cmoBtFADryP3INAGrKAAWyZX7R%2BSgd4B6FACPxEy9mOnmvSIdBcANcbIse355J4lMAfCTuYHVIaS8w8ShALhc5qWSPPLOM5EC6O78ABI99/gsOJkC6OvMuBE0a/l0OIECaOe0ZBEro/jIOIgCaOScHBEix/EJMpYCaOHo4BAZ5/OZsp8CKO7QmJAREfiI2UwBlHVcLgiFmHzirKUAChIEy/3z198fvpQ6Aj59lvt99gtgpIMOv5OfyMuHNfxiuH5BF0MlJoAijoj%2B8kf9n7/%2Bvv6XYkPAG64N7vlt9gtggOEn/P3nT054GUd8mnF%2ByR17WAHldkT0j/2CBHH9ZAdeMDZCBSiArMZGv2PcxPAnBGogNc8A8hH9Q7w8ALiq/RjgHtdSc54BJDPwxFr0M/Ya8GAgHSugNMZG/6gvRQEDHw/YCOViBZTDqPR3Mq/e7H%2Buem6B3nCltWICiM6B5EyjpgGjQAqeAYQ2JP3t%2Bllr1DXjqUBwJoCgRkX//i9CW0OmAaNAZJ4BRLQ//Z23B24%2BALjyGOAe12RJJoBYHDNi2j8NGAUC8gwgEOlPcPsvME8FQrECCkH0n%2BbB/ufKFmgJV2wNJoD5dp4l3%2BTD%2BfZfdUaBCBTAZPvTf9QrgbV0QHYeAk8j%2Bilg58NhT4bn8gxgjj3p77Rs9vQBwJXHANu4qtOxAprAOaGkPRenddAUVkCnEv3UtmcjZB10PhPAeaT/XAv3P%2BxnFMjCM4CTbL6sRf8oqwrAY4AhXPbBmQDO4BjQ0%2BYL2BxwDhPAsax9gli7/zEBDOQUhKUADuTGP44NDwB0wFiOQ0BWQEdxucNr1kEBKYBDSH/4lQ6IxgpovG0Xq%2Bg/zrZvALUCOo4zEoQJYDBXdhl%2BbuA42y54c8BwCmAk6Q8L6YAIrIDGEP1h7bmRtwU6gbMzkQlgAFdwVbZAJzAKTKQA9pL%2BsJMOmEUB7CL9YQgdMIUC2E76x2eHk4gOOJ%2BHwBttuOxE//mGFIBHwSdzuE5jAtjCBQrH2XBYzAHbKIDVpH8W9j956YBzKIB1pH9DimQKHXACBbCC9Icz6YCjKYClpD%2BcTwccSgEsIv3TsbcpQwccRwE8J/1RJ3PpgIMogPGkPwznWB1BATyx9j7CZRqBG/aS1h4uQ8BTCuAR6c8LpRKBDhhLAdwl/SEgHTCQArhN%2BkNYOmAUBXCD9E/NrqYDHTCEAnhL%2BnOPaglFB%2BynAH4i/SERHbCTAthO%2BgfkJr0bx3APBfCfVXcHLrueFExAqw6jIeA1BfAv6Q956YBtFMDlIv0hPx2wgQJwKdRhP8NyDv5FAazl9h81E5bjuVb3ArD8gUosglZpXQDSvxI35lzpgOX6FoD0h6p0wEJ9C2A56c8bpo34HNslmhZA584H3mgbCB0LwPKnHrfk/Moi6Kl2BSD9GULlpKADHmtXAMtJfyjAQX6gVwE0bPgO3IwzSreIaFQAlj/Qk0XQPY0KYDnpzxImj0Qc6pu6FMDyVnehQEnLj3afIaBFAfT5OBtyG84RmoRGiwJYzu0/q6ifXBzwN%2BoXgOUP8MIi6LXiBSD9a3MDzgY64EXxAgDgnsoF4PafE5hCMjIEXJUtAOlfnuRlDx1wKVwAADxWswDc/nMms0hShoCCBSD9gYWad0DBAqADN92wX7UCcPsPrNJ5CKhWADCFiYSMShWA2/8mpC1jtR0CShXAQtIfeKNnLNQpgGLNTDrmkiYqRU2RArD8AXZquAgqUgD04UYbRqlQAG7/gSG6DQEVCmAh6c/RTCcFtAqK9AVQo4dZSMISR4HwSV8AC7VqdWCPPnGRuwAKNDCQV/YIyl0AC/Xpc6azpKqhSWgkLoDs3ctaspWAUgdR4gJYqEmTA2N1iI6sBZC6danNpNJN3jjKWgALdejwJqQq5ysfICkLIG/fAiUlDaWUBbBQ%2BfYGjlY7RvIVQNKmpRULq4YyRlO%2BAliodm93I0%2BZqHCYlC0AAB5LVgALh6zCjU0WppZKFkZKui1QsgKgIUkKB8lUAG7/gVlKDgGZCgCAgdIUgNt/0rG8KqbeEJCmAOhJhsJxFABAUzkKwP6HpEwwxRTbAuUoAHqSnnCoBAXg9h%2BIo9IQkKAAADhCkQJw%2B09YFln1lAmc6AWQYoziCHKT7OLHV/QCAOAgFQqgzDhGVaaZemrETugCiD9AcRCJSQ3BQyx0AQBwnPQFUGMQA9IpED5xCyD46ASrWGq1FTnK4hbAEgUamF/JSrLIHkG5CwCAzYIWQOShCbYx2bQVNtCCFsAS2YcvbpKS5JI6iBIXAAB7RCyAsOMSwDYxYy1iASyReuzinvL7n/L/wJ7yxlHWAgBgp3AFEHNQAtgpYLiFKwAAzpGyAPJu3HigyX68yT%2Bzm6ShlLIAANgvVgEE3JEBjBIt4mIVwBJJRy0ea7UYafWP7SNjNOUrAACGCFQA0YYjgOFCBV2gAgDgTMkKIOOWjaca7sQb/pM7SBdQyQoAgFEUAEBTUQog1IMRztR2GdL2H06cuItSAEuk268B3eSKqUwFAMBACgCgqRAFEGcjxsma78Gb//M7CxJ6IQpgiVybNaCtRGH1%2B%2BwXQFNufq%2Bu78OHLx9nvxA6UgCcTfT/Sg0wRZoVEDVI/we8OZxs/gQQ5GEIR5NuSxgF%2Bvj%2B9dv0pwXzC2CJ6W8Te4j%2BtdRAdu8/f0pxa5ujAEhK9O%2BhBjiaZwAcRfoP4W3kOCYAxpNZYxkFOIgCYCTRfxw1wHCTCyDFcxKWEP3nUAOVTP9GoATPAHwLUHzS/2Te8PhSBJcVELtIolmMAuynANhI9EegBthDAbCa6I9GDbBNgmcAhCL9w/LRsJYJgKXkS3xGAVZRADwn%2BnNRAyz07v0f066SJT8EkOJbqQoT/dmpgbmCp5xnANwl/Qv456%2B/fY7cowC4QWoU49PkJs8A%2BImkqMqDAX6lAPiX6O9ADfCaFRCXi/RvxoqPKwXQnSxoy%2BeOFVBfzj82Qs0pgI5EP6%2BpgbasgNqR/txkGdjQtALwt8DO54TzlCvkfBPDMPQKyO%2BBGMWpZjkboYHef/4U%2BWY3dAGwn%2BhnGzXQgWcAlUl/drI2rE0B1OTcMpBrqSoroGqcVY5gI1SSAqhD9HM0NVCMFVAR0p/TWDCWYQJIz1FkCtNAASaAxNyIMZ0rMDUTQEpOHXEYBfIyAeQj/QnIPJqRCSATB4zgTAO5mABycHtFIq7VLEwA0TlLZGQUSMEEEJr0JzWTa3AmgKAcG8owDYRlAgjHTRMluaoDMgEE4oRQm1EgGhNAFNKfJsy4cZgA5nMYaMg0EIEJYCa3QjTn%2Bp/LBDCH6x6ujAITmQAmkP7whml4ChPAqVzi8IBp4GQK4CSiHxZSA6exAjqc2RY2cGpOoACO5SKGzdw8Hc0K6CguXBjCRug4oQvg%2B9dv7z9/mv0qVhP9MFzSGvj%2B9dvsl/DItBVQxmR/ysQKhyp5viaGoWcAw5S8NCEat1kDhV4BZeFyhJMl3QhFowB2Ef0wkRrYyQpoI3MoBOEkbqYAtnDBQShuyLaxAlrHRQZh2QitpQCWEv2QghpYzgroOdMlpOPMLqEAnnAZQVJu3Z569/6PmYPSkp%2BTnvVjci4dKGPKRihyvl15BnCD6IdiPBi4SQH8RPRDYWrgDc8A/iP9oQMn/YUJ4HJxQUAzRoGr7gUg%2BqEtNdC3AEQ/cOldAwmeARzxJ3WkP/Da8EwI/rfAriZPAO8/fzr5bRL9wE3njwLT/zBioxWQ6AeearURalEAoh9YpUkNJHgGsJP0B7Ypnx6VJ4DyHx5wtNqjQI4C%2BP7126qnJaIfGGhtDaT4FqBLhAIY%2B41Aoh84yNhpYPq3AF2KPQOQ/sDRKuXM/AlgiEofCRBcmQcD6QtA9ANTFKiBNCugLA9VWOjDl4%2BpT84o3od6EoVViAng/F8IwRSS7p7X74yhtoMIT4AvQQqA2uT%2BKi9vlybgaAqAQwj9/YwFHC1TAaz9cTDOJ/cPYizIItc2O0oBeAyQl9A/k7GggDg3slEKgHTk/nTGAnZSAKwg9GMyFrBNsgLwGGAKuZ%2BIsWCidHvsZAXAaYR%2BdsYCngpUAJ4DRyD3SzIWxBFqhxGoAJhF6PdhLOC1fAXgMcAocr85Y8FYGRcYsQrAFuhoQp9fGQtOE%2B3mNVYBcBC5z0LGglZSFoAt0EJyn82MBaskXV2kLAAeEPoMZyyoKlwBeAywjdznBMaCPQLuLcIVAMsJfSYyFhSQtQA6PwaQ%2B4RiLMi7tIhYALZAvxL6pGAsuCfmDWvEAuCF3CcpY0EKiQug6hZI6FNM7bEg9boiaAE03ALJfcprOxaEvVUNWgBNCH3aqj0WZJG7AL5//Xb537vZr2I1uQ8v2o4FEcQtgGJbIKEPT5UcC8Lufy6RC6AGuQ8bGAvOoQAOIfdhlJJjQRChCyDXFkjow6EyjgWR9z%2BX4AWQgtyH8xkLhlAAWwh9CCLjWBBH9AIItQWS%2BxBZtLEg%2BP7nEr8AphP6kI6xYCEFcJvchxqijQWhJCiA07ZAQh8KO3ksiL//uaQogKPJfejGWHCVowCGDwFCH7gcNhakuP2/ZCmAUeQ%2BcE/DsaB%2BAQh9YJU%2B30SUpgDWboHkPrDfhrEgy/7nkqgAlnj3549LqncfyOLDl48v96A/Ev4Zkpt%2Bm/0CVriX7O/%2B/HH9z/V/xvnJYaCM18HyJnNey3UDmqkAbrr5GQCcIHv%2BJCuAhe1qCAAGWhgpuW7/L%2BkKAIBRyhaAIQAYonCY5CuAdEMW0EHGaMpXAMsV7m3gHLVjJGUBZGxaoLCkoZSyAJar3d7AocoHSNYCSNq3QD154yhrASxXvsOBI3SIjsQFkLd1gTJSB1HiAliuQ5MDAzUJjdwFkLp7geyyR1DuAliuSZ8D%2B/WJi/QFkL2BgaQKhE/6AliuT6sDm7UKigoFsLyHW320wFrLI6LA7f%2BlRgEAsEGRAjAEADt1u/2/lCmAS6GPBIisUtTUKYDlDAHAGz1joVQBWAQBGzRc/lyVKgAAlqtWAIYAYJW2t/%2BXegUAwEIFC8AQACzU%2Bfb/UrIALjoAWKB5%2Bl%2BqFgAAT5UtAEMA8IDb/0vhArjoAOAO6X9VuQAAeKB4ARgCgDfc/r8oXgAXHQC8Iv1fq18Aq%2BgAKMwBf6NFAXRocmCgJqHRogAuFkHQnuXPr7oUwCo6AIpxqG9qVACrWt3lAmWsOs59bv8vrQrg0uyjBdbqFhG9CmAVQwAU4CA/0K4ALIKgD8ufx9oVwEUHQA/S/6mOBXDp%2BmEDN7UNhKYFsIohANJxbJfoWwAWQVCV5c9CfQvgogOgIum/XOsCuOgAqEX6r9K9ANbSARCW47mWAnAXAB05%2BBcFcGURBNlZ/mygAP6lAyAv6b%2BNAviPDoCMpP9mCmA7HQDTOYZ7KICfrL07cPHBRGsPoNv/NxTAWzoAUpD%2B%2BymAG3QABCf9h1AAt%2BkACEv6j6IA7tIBEJD0H0gBPKIDIBTpP5YCeEIHQBDSfzgFMJ4OgOEcqyMogOc23Ee4WGGgDQfK7f8SCmARHQCzSP/jKICldACcT/ofSgGsoAPG%2Buevv2e/hPm8CQ9I/6O9e//Hx9mvIRkX5X5S71cfvjiJP3HQTmACWM0csJP0v8nb8pr0P4cC2EIHbCbmHvDmXEn/01gBbbct09teqdJtubbrIGfqZCaA7bZddj1HAem/Ss%2B3S/qfTwHsogOW6BlnO3V706T/FFZAA7h27%2BmWYkfosA5ygmYxAQxgDrhJ%2Bg9R/m2U/hOZAEZyKb8oH1snKzkHOC/TKYDBXNOi/ziVasBJicAKaLDm6yDpf6gyb6/0D8IEcIjNgZ76Ei8TT8GlngN6Ho2wFMBRWl3oov98GWug1aFIwQroKJsv2XTrIOk/Rbq3XfoHZAI41p40T3Hdp4uhYlLMAeVPQV4K4Awl731EfxyRa6DkxV%2BGFdAZ6q2DpH8oYT8O6R%2BcCeA8NQbhsFnDJdIoUONqL88EcJ49l3WQUUD6BxfkA5L%2BWZgAJkh6PIKEC09NnAOSXtttKYA5cp0T0Z/R%2BTWQ66rmogAm2rnVOe3ASP%2B8TuuALBczbyiAyYKfHOmf3dEdEPwC5jEFMF/MIyT6KzmoBmJeuiynAELY/00%2BY8%2BS9K9nbAdEu2LZRgEEEuRQSf%2BqhnRAkKuUIRRALHNPl%2BjvYE8NSP9iFEBEU46Z9O9jQweI/pIUQFBDfvR3%2BZGT/t0s74CTL0XOpABCO%2BHsif7OHteA6C9PAUQ36rcA3TyH0p%2BbHXDoVUccv89%2BATxxPUL7D%2BT1KziQVzdTTx1eRH8zJoA0Bv5C0JfD2SryVj357PPOvLwtR1xgBKcAkhl7SsvH3JDvfK/9Ln348lH0t6UA8hl4XH/8792oLxXHob/9pl4ZvPvzx6gvJf3TUQBZDamBMgUw5Tfg1yiDIQUg%2BpNSALntrIG8BRDnbx9e5S2DnQUg%2BlNTABVsroFcBRAt9O/JVQabC0D0F6AAitjWAfELIEvo3xO/DLYVgPSvQQGUsrYGYhZA9tC/J2YZrC0A0V%2BJAihoeQ3EKYCqoX9PnDJYXgCivx4FUNaSGphbAN1C/4GJfbCkAER/VQqguMc1cH4BCP2nTi6DxwUg%2BmtTAC3cq4FzCkDob3ZCGdwrANHfgQJo5NcaOK4AhP5wB5XBrwUg%2BvtQAO28roGxBfAmSuTIKIc29%2BtPzUfWjQLo6/vXbztzxDeQHOe0b%2BV69%2BcPn05bCqC1DVuF/b86Rtzcs//3O20oA8u6zvxBGJ4b%2BAsjLz/HnDIY%2BLtdLz9/UnF%2ByIOwFAC3jQ39e97EX4c%2BGJv4DygDnlIA/OeIPw61yq//v9krYdY7%2BcbrRX%2BcH0JmOs8AWvvnr78fr4CD5NcbMVsh43v19AKgNgXAIjHT7Z4jGsI7QD0KgHVy5WA3cp9VFAAbaYI45D7bKAD20gSzyH12UgAMownOIfcZRQFwCGUwltDnCAqAY2mCPeQ%2Bh1IAnEofPCbxOZMCYBplcCX0mUUBEEWfPpD4BKEAiKtGJYh7wlIA5BOzGAQ96SgAqjmuHkQ8xSgAgKZ%2Bm/0CAJhDAQA0pQAAmlIAAE0pAICmFABAUwoAoCkFANCUAgBoSgEANKUAAJpSAABNKQCAphQAQFMKAKApBQDQlAIAaEoBADSlAACaUgAATSkAgKYUAEBTCgCgKQUA0JQCAGhKAQA0pQAAmlIAAE0pAICmFABAUwoAoCkFANCUAgBoSgEANKUAAJpSAABNKQCAphQAQFMKAKCp/wPyL1MBuoTXJAAAAABJRU5ErkJggg%3D%3D%22%2C%20%22sizes%22%3A%20%22512x512%22%2C%20%22type%22%3A%20%22image/png%22%7D%5D%7D\">\n<link rel=\"apple-touch-icon\" href=\"data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAALQAAAC0CAIAAACyr5FlAAAHPUlEQVR4nO2dTW7jOBCF6cGs3EADA3QOkSv0/ZEr5BAJMKtk27MgIHAslSyR9fOKet9qEKDHUvHzq5JsU7f7z1+FkC3+ij4AggvlICKUg4hQDiJCOYgI5SAilIOIUA4iQjmICOUgIpSDiFAOIkI5iMjf0QcQwPf7R8e/ur++qB8JOLfpP7LvU+EI0+sypxx2QkhMKco8cvgLITGNKOnl8BkgrjmmJJbj4ILZrVD4AViTT44jS+K/HphHNUgmOZ4uAEL1UxzkQXLIsV9xxXJ/vX3++K1TELdjtgP9JthOicHruxze5inUP4KfAnRySGYY1fTr7bP+h1Z4tDifiwqgyZGxlPvUI1+fF3KEwMkxnxYtuRTB+lR204z76wta1QaRzgjnJm8FaOZYl8bTiWXgqFiMHZvEnvU+EMnx/f6BXCNT1qe5WY0Q4uXY1OIiZlQ2zxfBj2A5QALjoads/sUaQD/C5LhyK5FAazExcrCVSEC1mAA5GBhPAfHDWw5AM6Txwn/saEHww1UOQDOQCffDTw6a0UGsH053SB9OCUeLp73D7VbpPiEF9EgOWDMS8VA0n/wwlyP8Ts6sOBTW+2qFsdGNf+ls5QBvKEcuVmMvaB9wbi6GcoCbkRRPP6zkoBl2uPnhMXNgmnG8X0B1lkriS1leoThjVHB9OdhQfHBoLspy0AxPrP0wnDmQzTg7RgCOHRXTImvKwVEjHN0lsEoO5NiYDLtSq8nROksznGkLrhgeOnLkaih9AwTs2LFGazn02wpjIwSLsivIkSs2LoLKoignB35sjHQH8M6iXvxRORgbsIwvjWZy4MfG9OguwZAcjA1wBhdILTlSxMb40AA+dhTVhYjfgoHA0i8Hb4nConXD9ELJodUR8DuLFp1ycBRNRPdiKSQHewogKotyobZCztIjR8aeojsopBs7+pZsNDnYU2AZXxq2FSJyCTksukC6ztLBaTl47ysRg3fDLpEcpA/KQUTml8NuOJh+7DgnBweOdIyMHXBPalLE4Z1dXwJkx0F15mwrX2+fnpk/a3+ZUI6QpXLW0Yep2kr48kzWZSaRI1yLlmkUOdFWMD+Mhc1zzKM6tYidMwfIdSzmAiyAiNu9WFnbCkLRD5K3y+STI5EWLRkVyXQpC5LSI+Q6/jRy5CrrDokUT9BWspTyFCm6DLQcU2rRAq4IaFtJlL3jwJ4pohywxbID882A1VYAC+QJWpdBSQ7Mt04IOHWITw6cWuAAEiGRclCLfcIVCWsrNOMggQ03QA6OFx2EVMy1rdCJEfy7TKcc3+8fp74lQC206FDEY2ef7u+M0Ax1ulvzqUW0nTk4XphiXVurmYNO+GA6iOjLQS38MVJEua3QjEDUm7iaHBwvQFBchdv957ksWv/Qnk5gUrvMyMYI8R+8GbE0YFN366vM+vaYTY6Qj6naF51JlBnkCP9ou8UnsXw4Lcf99WVpY2dvousC5cQahDgZ3IkpWXKACyGRNE5yyJHUiTUIcXKcUTm+3z/KvzeVQ3lgGiEkrONkfMuMHjnasUOd6Z1Y4xAnfaMhRFu5oBASUNNJpBx0YgeE6aRTju7OQiE6GIwT9J196IQKznHSL8fT8KAQphyMk5G7lPrJQSecsYsTHTlu//wpMFsMXpkfv3/VOP+jcfNp6Ms+1YZqBoFC5e2q+TVBzF1sL4XuEvDRodMC9+hQhkcg6sXns+znBPRZ9gyPECzKriMHwwMKreVQS47B59uSEYwezGj1Q2r64YZdqTXlYHMJR3cJDLdgYHg4YFpkZTkezKUfpjyUVz259ZODfvhgbUYxaiscPpwxKrjHVpMMD3V8SmolB5uLHQ4NpWKYHPTDAjczinVboR+6eJpR/Le3ph/d+JfOXA5euRjhUFiP5GBzGce5oVSc2sraDypykHWt3MLYb+ZYn5KDH9Y/C7P+/69L5NmmT281OYjb2Tr/+Njip1yxZhT/qxWf/PD/Wbr6K4abUUKe1GTtR9SGBYqvi2BG8W8rC5tCDJYAYcOTMtZiLMrSTZgcFcW3CIgZlT4/QAJjIViOolERKC1aBh+2FX7/MF6OMpalsGZUjvgB1UpaIOSodLx1wM2o7PsBGBgLQHKUM++hFFq0rBWBDYwFLDmKfFnbVi2dGZXFjyPniADEPqQttUDr8tW/GJVvM/ktFMyiRQUuOVqkUqrsaXTqUkJFlM0tkDC1qEDLUQQ/RuQY/BBkxJK1HMhmFHw5Kg+KnJXDaIPDs6K0coBrUckhR2VR5IgczjteHhEl3Z6LcAPpDtKsurC8Nf0XoE0Fyd1EWlQyyVG5v76Ut//9Zd3Ljfar2HmVzeNRGZwDySdH5ek9gwWVe03jTwHIeG8m08yxD86XUtO1D4l55GjxF2UaIVrmlKPFTpQphWiZX441fbpMr8KaK8pBDhLwBWOSBcpBRCgHEaEcRIRyEBHKQUQoBxGhHESEchARykFEKAcRoRxEhHIQkf8AP/y3SqdFgTQAAAAASUVORK5CYII=\">\n<style>:root{--bg:#0d1015;--panel:#141920;--panel2:#1b212a;--line:#272f3a;--fg:#e7ebf0;--mut:#8893a1;--acc:#4d8dff;--ok:#3ecf8e;--warn:#e5a23c;--bad:#e5594f}\n*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}\nhtml,body{margin:0;height:100%;background:var(--bg);color:var(--fg);font:15px/1.35 system-ui,-apple-system,\"Segoe UI\",Roboto,sans-serif;overflow:hidden}\nbody{display:flex;flex-direction:column;padding:env(safe-area-inset-top) env(safe-area-inset-right) env(safe-area-inset-bottom) env(safe-area-inset-left)}\nheader{display:flex;justify-content:space-between;align-items:center;height:44px;padding:0 10px;background:var(--panel);border-bottom:1px solid var(--line);gap:8px}\nnav{display:flex;gap:2px;height:100%}\nnav button{background:none;border:0;border-bottom:2px solid transparent;border-radius:0;color:var(--mut);padding:0 14px;min-height:0;height:100%;font-weight:500}\nnav button.on{color:var(--fg);border-bottom-color:var(--acc)}\n#ptitle{display:none;font-weight:600;letter-spacing:.2px}\nbutton{font:inherit;color:var(--fg);background:var(--panel2);border:1px solid var(--line);border-radius:8px;min-height:38px;padding:0 14px;cursor:pointer}\nbutton:active{background:#232b36}\nbutton:disabled{opacity:.4}\nbutton.ic{width:38px;padding:0;display:inline-flex;align-items:center;justify-content:center}\nbutton.ic svg,#fsbtn svg{width:20px;height:20px;fill:none;stroke:currentColor;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round}\n#status{display:flex;align-items:center;gap:8px;white-space:nowrap;color:var(--mut);font-size:13px}\n#dot{width:8px;height:8px;border-radius:50%;background:#555}\n#dot.ok{background:var(--ok)}#dot.warn{background:var(--warn)}#dot.bad{background:var(--bad)}\n#gear{background:none;border-color:transparent}\nmain{flex:1;position:relative;min-height:0}\n.tab{position:absolute;inset:0;display:none}.tab.on{display:block}\n\n/* PFD */\n#pfdsvg{width:100%;height:100%;display:block;background:#000}\n#pbtns{position:absolute;right:8px;top:8px;z-index:5;display:flex;gap:6px}\n#pbtns button{background:rgba(13,16,21,.6);border-color:rgba(255,255,255,.18);width:40px;min-height:40px}\n#pback{display:none}\n.i-out{display:none}body.pfdfs .i-in{display:none}body.pfdfs .i-out{display:block}\nbody.pfdfs header{display:none}\nbody.pfdfs #pfd{position:fixed;inset:0;z-index:900;background:#000;padding:env(safe-area-inset-top) env(safe-area-inset-right) env(safe-area-inset-bottom) env(safe-area-inset-left)}\nbody.pfdfs{padding:0}\n/* phone in landscape: hide the header on the instruments screen so the PFD fills the screen */\n@media (max-height:520px) and (orientation:landscape){\n  body.t-pfd header{display:none}\n  body.t-pfd #pback{display:inline-flex}\n}\n\n/* autopilot: designed for a portrait phone, single column */\n#ap{overflow:auto;-webkit-overflow-scrolling:touch}\n#apwrap{display:flex;flex-direction:column;gap:10px;padding:10px;max-width:560px;margin:0 auto}\n#aprow{display:flex;gap:8px}\n#aprow button{flex:1;min-height:56px;font-size:15px;font-weight:600;letter-spacing:.5px;border-radius:10px;padding:0 6px}\n#aptog.on{border-color:var(--ok);color:var(--ok)}\n#pausebtn.paused{border-color:var(--warn);color:var(--warn)}\n#apmsg{min-height:20px;font-size:13px;color:var(--mut);line-height:1.3}\n#apmsg.ok{color:var(--ok)}#apmsg.bad{color:var(--bad)}\n#apgrid{display:flex;flex-direction:column;gap:10px}\n.apc{background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:10px;display:flex;flex-direction:column;gap:8px}\n.aph{display:flex;justify-content:space-between;align-items:center;gap:8px}\n.apl{display:block;font-size:11px;letter-spacing:1.2px;color:var(--mut);font-weight:600}\n.apv{display:flex;align-items:baseline;gap:5px}\n.apv b{font:600 28px ui-monospace,Menlo,monospace;color:var(--fg);line-height:1.1}\n.apv small{color:var(--mut)}\n.apr{display:flex;gap:4px;align-items:stretch}\n.apr button{flex:1 1 0;min-height:48px;padding:0 2px;font-size:15px}\n.apr input{flex:1.6 1 0;min-width:0;margin:0;padding:0 2px;text-align:center;font-weight:600;font-size:17px}\n.set,.pri{min-height:46px;background:var(--acc);border-color:var(--acc);color:#fff;font-weight:600}\n.set:active,.pri:active{background:#3d7be6}\n#ap.dis #apgrid,#ap.dis #aprow,#ap.dis #fplist{pointer-events:none;opacity:.45}\n.fph{display:flex;align-items:center;gap:8px;margin-top:6px}\n.fph h3{margin:0;font-size:12px;letter-spacing:1.2px;text-transform:uppercase;color:var(--mut);font-weight:600}\n#lnavtxt{flex:1;font-size:13px;color:var(--fg);min-width:0}\n#lnavstop{min-height:38px;color:var(--bad)}\n#fplist{display:flex;flex-direction:column;gap:6px;padding-bottom:16px}\n.fp{display:flex;align-items:center;gap:8px;background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:6px 6px 6px 12px}\n.fp.sel{background:var(--panel2);border-color:#cfd6dd}\n.fp.act{border-color:var(--acc)}\n.fp.done{opacity:.45}\n.fp .id{font:600 15px ui-monospace,Menlo,monospace;min-width:62px}\n.fp .mid{flex:1;font:12px ui-monospace,Menlo,monospace;color:var(--mut);min-width:0}\n.fp button{min-height:42px;min-width:72px}\n.soon{margin:8px 0;color:var(--mut);font-size:13px}\nbody.stale #pfdsvg{filter:grayscale(.85) brightness(.65)}\n\n/* phone in portrait: only the autopilot panel */\n@media (orientation:portrait) and (max-width:700px){\n  nav{display:none}#ptitle{display:block}#stxt{display:none}\n}\n\n/* dialog */\ndialog{background:var(--panel);color:var(--fg);border:1px solid var(--line);border-radius:12px;width:min(420px,92vw);max-height:92vh;overflow:auto}\ndialog::backdrop{background:rgba(0,0,0,.6)}\ndialog h3{margin:10px 0 6px;font-size:12px;letter-spacing:1.2px;text-transform:uppercase;color:var(--mut);font-weight:600}\ndialog p{font-size:13px;color:var(--mut)}\nlabel{display:block;margin:10px 0;font-size:13px;color:var(--mut)}\nlabel.chk{display:flex;align-items:center;gap:10px;font-size:14px;color:var(--fg)}\nlabel.chk input{width:20px;height:20px;margin:0}\ninput{display:block;width:100%;margin-top:4px;padding:10px;font:15px ui-monospace,monospace;background:var(--bg);color:var(--fg);border:1px solid var(--line);border-radius:8px}\n.row{display:flex;gap:8px;margin-top:14px}\n.row2{display:flex;gap:8px;margin:8px 0}.row2 button:first-child{flex:1}\n.hint{margin:4px 0}\n</style>\n<title>GeoFS Companion</title></head>\n<body>\n<header>\n  <nav><button data-tab=\"pfd\" class=\"on\">Instruments</button><button data-tab=\"ap\">Autopilot</button></nav>\n  <span id=\"ptitle\">Autopilot</span>\n  <div id=\"status\"><i id=\"dot\"></i><span id=\"stxt\">Not paired</span>\n    <button id=\"gear\" class=\"ic\" aria-label=\"Settings\"><svg viewBox=\"0 0 24 24\"><path d=\"M4 7h9M17 7h3M4 17h3M11 17h9M13 4v6M7 14v6\"/></svg></button></div>\n</header>\n<main>\n  <section id=\"pfd\" class=\"tab on\">\n    <svg id=\"pfdsvg\" viewBox=\"0 0 820 400\" preserveAspectRatio=\"xMidYMid meet\"></svg>\n    <div id=\"pbtns\">\n      <button id=\"pback\" class=\"ic\" aria-label=\"Go to autopilot\"><svg viewBox=\"0 0 24 24\"><path d=\"M15 5l-7 7 7 7\"/></svg></button>\n      <button id=\"fsbtn\" class=\"ic\" aria-label=\"Fullscreen\"><svg class=\"i-in\" viewBox=\"0 0 24 24\"><path d=\"M4 9V4h5M20 9V4h-5M4 15v5h5M20 15v5h-5\"/></svg><svg class=\"i-out\" viewBox=\"0 0 24 24\"><path d=\"M9 4v5H4M15 4v5h5M9 20v-5H4M15 20v-5h5\"/></svg></button>\n    </div>\n  </section>\n  <section id=\"ap\" class=\"tab\">\n    <div id=\"apwrap\">\n      <div id=\"aprow\"><button id=\"aptog\">AUTOPILOT: \u2014</button><button id=\"pausebtn\">PAUSE</button></div>\n      <div id=\"apmsg\"></div>\n      <div id=\"apgrid\"></div>\n      <div class=\"fph\"><h3>Flight plan</h3><span id=\"lnavtxt\"></span><button id=\"lnavstop\" hidden>Stop direct</button></div>\n      <p class=\"soon\" id=\"fphint\">Tap a waypoint to point the magenta marker on the PFD at it (the autopilot does nothing). Direct makes the autopilot fly there.</p>\n      <div id=\"fplist\"><p class=\"soon\">No flight plan found in GeoFS.</p></div>\n    </div>\n  </section>\n</main>\n<dialog id=\"pair\"><form method=\"dialog\">\n  <h3>Pairing</h3>\n  <p>Scan the QR from the userscript, or paste the details here. If you paste the whole link into one of the fields, both are filled in.</p>\n  <label>Peer-ID<input id=\"ipeer\" autocapitalize=\"off\" autocorrect=\"off\"></label>\n  <label>Token<input id=\"itoken\" autocapitalize=\"off\" autocorrect=\"off\"></label>\n  <p id=\"wlnote\" hidden>Wake Lock not available: turn off auto-lock in your phone settings.</p>\n  <h3>Instruments</h3>\n  <label class=\"chk\"><input type=\"checkbox\" id=\"ipitch\"> Invert pitch</label>\n  <label class=\"chk\"><input type=\"checkbox\" id=\"iroll\"> Invert roll</label>\n  <div class=\"row2\"><button type=\"button\" id=\"pcal\">Calibrate pitch (currently level)</button><button type=\"button\" id=\"pcalreset\">Reset</button></div>\n  <p id=\"pcalv\" class=\"hint\"></p>\n  <div class=\"row\"><button id=\"save\" class=\"pri\" value=\"ok\">Pair</button><button id=\"unpair\" value=\"x\">Unpair</button><button value=\"c\">Close</button></div>\n</form></dialog>\n<script src=\"https://unpkg.com/peerjs@1.5.4/dist/peerjs.min.js\"></script>\n<script>// Transport layer. Interface: connect(pairing), disconnect(), send(msg), onMessage(cb), onStatus(cb)\n// status: 'disconnected' | 'connecting' | 'connected'. Replace this class with a WebSocket/TURN variant of the same shape.\nclass PeerTransport {\n  constructor(opts) { this.opts = opts || {}; this.msgCb = () => {}; this.stCb = () => {}; this.attempt = 0; this.timer = null; this.stopped = true; this.ok = false; }\n  onMessage(cb) { this.msgCb = cb; }\n  onStatus(cb) { this.stCb = cb; }\n  connect(pairing) { this.pairing = pairing; this.stopped = false; this.attempt = 0; this._open(); }\n  disconnect() { this.stopped = true; clearTimeout(this.timer); this.timer = null; this._close(); this.stCb('disconnected'); }\n  send(msg) { if (this.ok && this.conn && this.conn.open) try { this.conn.send(msg); } catch (e) { /* ignore */ } }\n  _close() { const c = this.conn, p = this.peer; this.conn = this.peer = null; this.ok = false; try { c && c.close(); } catch (e) {} try { p && p.destroy(); } catch (e) {} }\n  _retry() {\n    if (this.stopped || this.timer) return;\n    const d = Math.min(30000, 1000 * 2 ** this.attempt++); // exponenti\u00eble backoff\n    this.timer = setTimeout(() => { this.timer = null; this._open(); }, d);\n    this._close(); this.stCb('connecting');\n  }\n  _open() {\n    this._close(); this.stCb('connecting');\n    const p = (this.peer = new Peer(undefined, this.opts));\n    p.on('open', () => {\n      if (this.peer !== p) return;\n      const c = (this.conn = p.connect(this.pairing.peer, { reliable: true }));\n      c.on('open', () => c.send({ t: 'hello', token: this.pairing.token, dev: this.pairing.dev, v: 1 }));\n      c.on('data', (m) => { if (this.conn !== c) return; if (m && m.t === 'hello_ok') { this.ok = true; this.attempt = 0; this.stCb('connected'); } else this.msgCb(m); });\n      c.on('close', () => { if (this.conn === c) this._retry(); });\n      c.on('error', () => { if (this.conn === c) this._retry(); });\n    });\n    p.on('error', () => { if (this.peer === p) this._retry(); });\n    p.on('disconnected', () => { if (this.peer === p && !(this.conn && this.conn.open)) this._retry(); });\n  }\n}\n</script>\n<script>(() => {\n  const $ = (s) => document.querySelector(s), LS = localStorage;\n  const CFG = { peer: { config: { iceServers: [{ urls: 'stun:stun.l.google.com:19302' } /* TURN hier toevoegen */] } }, staleMs: 2500, delayMs: 250, ackMs: 4000 };\n  LS.dev = LS.dev || (crypto.randomUUID ? crypto.randomUUID() : String(Math.random()).slice(2) + Date.now());\n  const esc = (s) => String(s).replace(/[&<>\"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '\"': '&quot;', \"'\": '&#39;' }[c]));\n  const D2R = Math.PI / 180;\n  const brgTo = (la1, lo1, la2, lo2) => { const p1 = la1 * D2R, p2 = la2 * D2R, dl = (lo2 - lo1) * D2R; return ((Math.atan2(Math.sin(dl) * Math.cos(p2), Math.cos(p1) * Math.sin(p2) - Math.sin(p1) * Math.cos(p2) * Math.cos(dl)) / D2R) + 360) % 360; };\n  const distNm = (la1, lo1, la2, lo2) => { const p1 = la1 * D2R, p2 = la2 * D2R, a = Math.sin((p2 - p1) / 2) ** 2 + Math.cos(p1) * Math.cos(p2) * Math.sin((lo2 - lo1) * D2R / 2) ** 2; return 2 * 3440.065 * Math.asin(Math.min(1, Math.sqrt(a))); };\n\n  // ---------- pairing ----------\n  // Accepts a whole pairing link (\u2026#peer=\u2026&token=\u2026) or separate values\n  function parsePair(str) {\n    const p = /[#&?]peer=([^&\\s]+)/.exec(str || ''), t = /[#&?]token=([^&\\s]+)/.exec(str || '');\n    return p && t ? { peer: decodeURIComponent(p[1]), token: decodeURIComponent(t[1]) } : null;\n  }\n  function readHash() {\n    const r = parsePair(location.hash);\n    if (r) { LS.peer = r.peer; LS.token = r.token; history.replaceState(null, '', location.pathname + location.search); return true; }\n    return false;\n  }\n  const tr = new PeerTransport(CFG.peer);\n  let conn = 'disconnected', lastRx = 0;\n  const isStale = () => conn === 'connected' && performance.now() - lastRx > CFG.staleMs;\n  const canSend = () => conn === 'connected' && !isStale();\n  function go() { tr.disconnect(); if (LS.peer && LS.token) tr.connect({ peer: LS.peer, token: LS.token, dev: LS.dev }); paint(); }\n  tr.onStatus((s) => { conn = s; if (s === 'connected') lastRx = performance.now(); paint(); });\n  tr.onMessage((m) => {\n    lastRx = performance.now();\n    if (!m) return;\n    if (m.t === 'state') pushState(m); else if (m.t === 'ack') onAck(m); else if (m.t === 'plan') setPlan(m.wps);\n  });\n  setInterval(() => tr.send({ t: 'ping', ts: Date.now() }), 2000);\n\n  function paint() {\n    const stale = isStale();\n    const [c, t] = !LS.peer ? ['', 'Not paired'] : conn === 'connected' ? (stale ? ['warn', 'Data stale'] : ['ok', 'Connected']) : conn === 'connecting' ? ['warn', 'Connecting\u2026'] : ['bad', 'Disconnected'];\n    $('#dot').className = c; $('#stxt').textContent = t;\n    document.body.classList.toggle('stale', stale || (!!LS.peer && conn !== 'connected'));\n  }\n  setInterval(paint, 500);\n\n  // ---------- instellingen ----------\n  // PFD corrections on top of SIGN in the userscript: inversion and pitch zero point\n  const sgn = () => ({ p: LS.invPitch === '1' ? -1 : 1, r: LS.invRoll === '1' ? -1 : 1 });\n  const pOff = () => { const v = parseFloat(LS.pitchOff); return isFinite(v) ? v : 0; };\n  const dlg = $('#pair');\n  const pcalTxt = () => { $('#pcalv').textContent = pOff() ? `Pitch zero point shifted by ${pOff().toFixed(2)}\u00b0` : 'No pitch correction active.'; };\n  $('#gear').onclick = () => {\n    $('#ipeer').value = LS.peer || ''; $('#itoken').value = LS.token || ''; $('#wlnote').hidden = 'wakeLock' in navigator;\n    $('#ipitch').checked = LS.invPitch === '1'; $('#iroll').checked = LS.invRoll === '1';\n    pcalTxt(); dlg.showModal();\n  };\n  $('#ipitch').onchange = (e) => { LS.invPitch = e.target.checked ? '1' : '0'; LS.pitchOff = '0'; pcalTxt(); };\n  $('#iroll').onchange = (e) => { LS.invRoll = e.target.checked ? '1' : '0'; };\n  // Calibrate: the current (level) pitch becomes the PFD zero point\n  $('#pcal').onclick = () => { const s = latestState(); if (!s) { $('#pcalv').textContent = 'No data received yet.'; return; } LS.pitchOff = String(s.pitch * sgn().p); pcalTxt(); };\n  $('#pcalreset').onclick = () => { LS.pitchOff = '0'; pcalTxt(); };\n  // If the whole link is pasted into one field, both fields are filled in\n  const onPaste = (e) => { const r = parsePair(e.target.value); if (r) { $('#ipeer').value = r.peer; $('#itoken').value = r.token; } };\n  $('#ipeer').addEventListener('input', onPaste); $('#itoken').addEventListener('input', onPaste);\n  $('#save').onclick = () => { LS.peer = $('#ipeer').value.trim(); LS.token = $('#itoken').value.trim(); go(); };\n  $('#unpair').onclick = () => { delete LS.peer; delete LS.token; go(); };\n  addEventListener('hashchange', () => { if (readHash()) go(); });\n\n  // ---------- tabs ----------\n  let tab = 'pfd', lastTab = 'pfd';\n  function setTab(t) {\n    tab = t;\n    document.querySelectorAll('nav button').forEach((x) => x.classList.toggle('on', x.dataset.tab === t));\n    document.querySelectorAll('.tab').forEach((x) => x.classList.toggle('on', x.id === t));\n    document.body.classList.toggle('t-pfd', t === 'pfd');\n  }\n  document.querySelectorAll('nav button').forEach((b) => b.onclick = () => { lastTab = b.dataset.tab; setTab(b.dataset.tab); });\n  $('#pback').onclick = () => { lastTab = 'ap'; setTab('ap'); };\n  // Phone in portrait: only the autopilot panel; in landscape the previous tab comes back\n  const portrait = matchMedia('(orientation: portrait) and (max-width: 700px)');\n  function applyOrient() {\n    if (portrait.matches) { if (tab !== 'ap') lastTab = tab; if (document.body.classList.contains('pfdfs')) setFs(false); setTab('ap'); }\n    else if (lastTab !== 'ap') setTab(lastTab);\n  }\n  if (portrait.addEventListener) portrait.addEventListener('change', applyOrient); else portrait.addListener(applyOrient);\n\n  // ---------- state-buffer + interpolatie ----------\n  const buf = []; let off = null;\n  const Lr = (a, b, k) => a + (b - a) * k, An = (a, b, k) => a + ((((b - a) % 360) + 540) % 360 - 180) * k;\n  const Ln = (a, b, k) => (typeof a === 'number' && typeof b === 'number' ? Lr(a, b, k) : b);\n  function lerpState(a, b, k) {\n    return { lat: Lr(a.lat, b.lat, k), lon: Lr(a.lon, b.lon, k), alt: Lr(a.alt, b.alt, k), ias: Lr(a.ias, b.ias, k), gs: Lr(a.gs, b.gs, k),\n      vs: Lr(a.vs, b.vs, k), pitch: Lr(a.pitch, b.pitch, k), hdg: An(a.hdg, b.hdg, k), roll: An(a.roll, b.roll, k),\n      mach: Ln(a.mach, b.mach, k), hagl: Ln(a.hagl, b.hagl, k), paused: b.paused, ap: b.ap, nav: b.nav, lnav: b.lnav };\n  }\n  function pushState(m) {\n    if (buf.length && m.ts <= buf[buf.length - 1].ts) return;\n    const o = Date.now() - m.ts; // clock difference + latency; use the minimum (slowly adjusted) as the offset\n    off = off === null ? o : o < off ? o : off + (o - off) * 0.02;\n    buf.push(m); if (buf.length > 40) buf.shift();\n  }\n  function sample() {\n    if (!buf.length) return null;\n    const rt = Date.now() - off - CFG.delayMs;\n    for (let i = buf.length - 1; i > 0; i--) {\n      const a = buf[i - 1], b = buf[i];\n      if (rt >= a.ts) return rt >= b.ts ? Object.assign({}, b) : lerpState(a, b, (rt - a.ts) / (b.ts - a.ts));\n    }\n    return Object.assign({}, buf[0]);\n  }\n  // Extra-calm IAS for display: exponential filter on top of the one in the userscript\n  let siV = null, siT = 0;\n  function smoothIas(v, now) {\n    if (siV === null || now - siT > 1500) siV = v; else siV += (v - siV) * (1 - Math.exp(-Math.min(0.2, (now - siT) / 1000) / 0.6));\n    siT = now; return siV;\n  }\n  function latestState() { return buf.length ? buf[buf.length - 1] : null; }\n\n  // ---------- flightplan ----------\n  // selIdx = only selected (the PFD points to it, the autopilot does nothing); \"Direct\" makes the autopilot actually fly there.\n  let plan = [], actIdx = -1, actOn = false, selIdx = -1;\n  function setPlan(w) {\n    const prev = selIdx >= 0 && plan[selIdx] ? plan[selIdx].n : null;\n    plan = [];\n    if (Array.isArray(w)) for (const p of w.slice(0, 200)) if (p && isFinite(p.lat) && isFinite(p.lon)) plan.push({ n: String(p.n == null ? '' : p.n).slice(0, 12) || 'WPT', lat: +p.lat, lon: +p.lon, alt: isFinite(p.alt) ? +p.alt : null });\n    selIdx = prev ? plan.findIndex((x) => x.n === prev) : -1;\n    actIdx = -2; // forceer opnieuw tekenen\n    buildPlanList(); syncActive();\n  }\n  const listEl = $('#fplist');\n  function buildPlanList() {\n    if (!plan.length) { listEl.innerHTML = '<p class=\"soon\">Geen flightplan gevonden in GeoFS.</p>'; return; }\n    listEl.innerHTML = plan.map((p, i) => `<div class=\"fp\" data-i=\"${i}\"><span class=\"id\">${esc(p.n)}</span><span class=\"mid\"></span><button data-i=\"${i}\">Direct</button></div>`).join('');\n    paintSel();\n  }\n  function paintSel() { listEl.querySelectorAll('.fp').forEach((el, i) => el.classList.toggle('sel', i === selIdx)); }\n  // Marks the active (direct-to) waypoint in the list, only on change\n  function syncActive() {\n    const s = latestState(), ln = s && s.lnav, idx = ln && ln.on ? ln.idx : -1;\n    if (idx === actIdx && !!(ln && ln.on) === actOn) return;\n    actIdx = idx; actOn = !!(ln && ln.on);\n    listEl.querySelectorAll('.fp').forEach((el, i) => { el.classList.toggle('act', i === idx); el.classList.toggle('done', actOn && i < idx); });\n  }\n  setInterval(syncActive, 500);\n\n  // ---------- PFD (SVG, modelled on the reference photo) ----------\n  // viewBox 820x400. Attitude-venster x200..540, y60..280 (midden CX,CY). Snelheidstape links, hoogtetape rechts, VSI helemaal rechts, kompasboog onderaan.\n  const svg = $('#pfdsvg'), CX = 370, CY = 170, PPD = 3.8, SPPU = 2.4, APPU = 0.25, HALF = 130;\n  const SX0 = 70, SX1 = 170, AX0 = 590, AX1 = 690, TY0 = 40, TY1 = 300, RY = 576, RR = 250;\n  const MAUVE = '#9b8ea4', INK = '#241c2b', MAG = '#d24fd2';\n  const FONT = 'Arial,Helvetica,sans-serif';\n  let ladder = '';\n  for (let p = -40; p <= 40; p += 2.5) {\n    if (!p) continue;\n    const y = -p * PPD, big = p % 10 === 0, mid = p % 5 === 0, w = big ? 40 : mid ? 22 : 11;\n    ladder += `<line x1=\"${-w}\" x2=\"${w}\" y1=\"${y}\" y2=\"${y}\"/>`;\n    if (big) ladder += `<text stroke=\"none\" x=\"${w + 6}\" y=\"${y + 5}\">${Math.abs(p)}</text><text stroke=\"none\" x=\"${-w - 6}\" y=\"${y + 5}\" text-anchor=\"end\">${Math.abs(p)}</text>`;\n  }\n  let rollTicks = '';\n  for (const a of [-60, -45, -30, -20, -10, 10, 20, 30, 45, 60]) rollTicks += `<line x1=\"0\" x2=\"0\" y1=\"-100\" y2=\"${-100 - (Math.abs(a) % 30 === 0 ? 10 : 6)}\" transform=\"rotate(${a})\"/>`;\n  // Niet-lineaire VSI: 0-1000 fpm 42 px, 1000-2000 fpm 27 px, 2000-6000 fpm 23 px\n  const vsY = (v) => { const a = Math.min(6000, Math.abs(v)), y = a <= 1000 ? a * 0.042 : a <= 2000 ? 42 + (a - 1000) * 0.027 : 69 + (a - 2000) * 0.00575; return v < 0 ? y : -y; };\n  let vsTicks = '';\n  for (const v of [500, 1000, 1500, 2000, 4000, 6000]) for (const sg of [1, -1]) {\n    const y = CY + vsY(sg * v), major = [1000, 2000, 6000].includes(v);\n    vsTicks += `<line x1=\"${major ? 728 : 726}\" x2=\"738\" y1=\"${y}\" y2=\"${y}\"/>` + (major ? `<text stroke=\"none\" x=\"710\" y=\"${y + 5}\">${v / 1000}</text>` : '');\n  }\n  const dia = (x, y, rx, ry) => `M${x} ${y - ry}L${x + rx} ${y}L${x} ${y + ry}L${x - rx} ${y}Z`;\n  let gsDots = '', locDots = '';\n  for (const k of [-2, -1, 0, 1, 2]) {\n    gsDots += k ? `<circle cx=\"565\" cy=\"${CY + k * 30}\" r=\"4\"/>` : `<line x1=\"553\" x2=\"577\" y1=\"${CY}\" y2=\"${CY}\"/>`;\n    locDots += k ? `<circle cx=\"${CX + k * 34}\" cy=\"297\" r=\"4\"/>` : `<line x1=\"${CX}\" x2=\"${CX}\" y1=\"288\" y2=\"306\"/>`;\n  }\n  svg.innerHTML = `<defs>\n<clipPath id=\"cAtt\"><rect x=\"200\" y=\"60\" width=\"340\" height=\"220\" rx=\"24\"/></clipPath>\n<clipPath id=\"cSpd\"><rect x=\"${SX0}\" y=\"${TY0}\" width=\"100\" height=\"${TY1 - TY0}\"/></clipPath>\n<clipPath id=\"cAlt\"><rect x=\"${AX0}\" y=\"${TY0}\" width=\"100\" height=\"${TY1 - TY0}\"/></clipPath>\n<clipPath id=\"cSD\"><rect x=\"122\" y=\"${CY - 24}\" width=\"36\" height=\"48\"/></clipPath>\n<clipPath id=\"cAD\"><rect x=\"653\" y=\"${CY - 26}\" width=\"48\" height=\"52\"/></clipPath>\n<clipPath id=\"cAll\"><rect width=\"820\" height=\"400\"/></clipPath></defs>\n<rect width=\"820\" height=\"400\" fill=\"#000\"/>\n<g font-family=\"${FONT}\">\n<g clip-path=\"url(#cAtt)\">\n  <g id=\"hz\"><rect x=\"-1500\" y=\"-1500\" width=\"3000\" height=\"1500\" fill=\"#3d9fe9\"/><rect x=\"-1500\" y=\"0\" width=\"3000\" height=\"1500\" fill=\"#c9a23f\"/><line x1=\"-1500\" x2=\"1500\" y1=\"0\" y2=\"0\" stroke=\"#fff\" stroke-width=\"2.5\"/></g>\n  <g id=\"hzl\" stroke=\"#fff\" stroke-width=\"2\" fill=\"#fff\" font-size=\"15\">${ladder}</g>\n</g>\n<g transform=\"translate(${CX},${CY})\" fill=\"none\" stroke=\"#fff\" stroke-width=\"2\"><path d=\"M-86.6 -50A100 100 0 0 1 86.6 -50\"/>${rollTicks}\n  <path d=\"M0 -99l-8 -11h16z\" fill=\"#000\" stroke=\"#fff\"/><g id=\"rp\"><path d=\"M0 -97l-9 15h18z\" fill=\"#000\" stroke=\"#fff\"/></g></g>\n<text id=\"ra\" x=\"540\" y=\"50\" fill=\"#fff\" font-size=\"20\" font-weight=\"700\" text-anchor=\"end\"></text>\n<g fill=\"none\" stroke-linejoin=\"miter\"><path d=\"M${CX - 112} ${CY}H${CX - 48}V${CY + 17}M${CX + 112} ${CY}H${CX + 48}V${CY + 17}\" stroke=\"#fff\" stroke-width=\"9\"/><path d=\"M${CX - 112} ${CY}H${CX - 48}V${CY + 17}M${CX + 112} ${CY}H${CX + 48}V${CY + 17}\" stroke=\"#000\" stroke-width=\"5\"/>\n<rect x=\"${CX - 4}\" y=\"${CY - 4}\" width=\"8\" height=\"8\" fill=\"#000\" stroke=\"#fff\" stroke-width=\"1.5\"/></g>\n<rect x=\"200\" y=\"6\" width=\"340\" height=\"26\" fill=\"${MAUVE}\"/><g stroke=\"#fff\" stroke-width=\"1.5\"><line x1=\"313.3\" x2=\"313.3\" y1=\"6\" y2=\"32\"/><line x1=\"426.7\" x2=\"426.7\" y1=\"6\" y2=\"32\"/></g>\n<g font-size=\"15\" font-weight=\"700\" fill=\"#fff\" text-anchor=\"middle\"><text id=\"f0\" x=\"256.7\" y=\"25\"></text><text id=\"f1\" x=\"370\" y=\"25\"></text><text id=\"f2\" x=\"483.3\" y=\"25\"></text></g>\n<rect x=\"${SX0}\" y=\"${TY0}\" width=\"100\" height=\"${TY1 - TY0}\" fill=\"${MAUVE}\"/>\n<g clip-path=\"url(#cSpd)\"><g id=\"st\"></g><g id=\"sb\"></g></g>\n<polygon points=\"58,${CY - 25} 158,${CY - 25} 170,${CY} 158,${CY + 25} 58,${CY + 25}\" fill=\"#000\" stroke=\"#fff\" stroke-width=\"2\"/>\n<text id=\"s10\" x=\"119\" y=\"${CY + 11}\" text-anchor=\"end\" font-size=\"30\" font-weight=\"700\" fill=\"#fff\"></text>\n<g clip-path=\"url(#cSD)\"><g id=\"sdr\" font-size=\"30\" font-weight=\"700\" fill=\"#fff\"></g></g>\n<rect x=\"${AX0}\" y=\"${TY0}\" width=\"100\" height=\"${TY1 - TY0}\" fill=\"${MAUVE}\"/>\n<g clip-path=\"url(#cAlt)\"><g id=\"at\"></g><g id=\"ab\"></g></g>\n<polygon points=\"578,${CY} 590,${CY - 27} 702,${CY - 27} 702,${CY + 27} 590,${CY + 27}\" fill=\"#000\" stroke=\"#fff\" stroke-width=\"2\"/>\n<text id=\"a100\" x=\"651\" y=\"${CY + 10}\" text-anchor=\"end\" font-size=\"30\" font-weight=\"700\" fill=\"#fff\"></text>\n<g clip-path=\"url(#cAD)\"><g id=\"adr\" font-size=\"24\" font-weight=\"700\" fill=\"#fff\"></g></g>\n<polygon points=\"704,${CY - 120} 738,${CY - 120} 750,${CY - 40} 750,${CY + 40} 738,${CY + 120} 704,${CY + 120}\" fill=\"${MAUVE}\"/>\n<g stroke=\"${INK}\" stroke-width=\"2\" fill=\"#fff\" font-size=\"15\" font-weight=\"700\">${vsTicks}</g>\n<g id=\"vb\"></g><path id=\"vn\" d=\"M750 ${CY}L716 ${CY}\" stroke=\"#fff\" stroke-width=\"3.5\" stroke-linecap=\"round\" fill=\"none\"/>\n<g id=\"glsc\" fill=\"#000\" stroke=\"#fff\" stroke-width=\"2\" display=\"none\">${gsDots}<path id=\"gsd\" d=\"\" fill=\"#fff\" stroke=\"none\"/></g>\n<g id=\"lcsc\" fill=\"#000\" stroke=\"#fff\" stroke-width=\"2\" display=\"none\">${locDots}<path id=\"lcd\" d=\"\" fill=\"#fff\" stroke=\"none\"/></g>\n<g clip-path=\"url(#cAll)\"><circle cx=\"${CX}\" cy=\"${RY}\" r=\"${RR}\" fill=\"${MAUVE}\"/><g id=\"hd\"></g><g id=\"hb\"></g></g>\n<path d=\"M${CX - 9} 305L${CX + 9} 305L${CX} 322Z\" fill=\"#000\" stroke=\"#fff\" stroke-width=\"2\"/>\n<text x=\"${SX0}\" y=\"338\" fill=\"#d6d6d6\" font-size=\"15\" font-weight=\"700\">GS</text><text id=\"gs\" x=\"${SX0 + 28}\" y=\"338\" fill=\"#fff\" font-size=\"22\" font-weight=\"700\"></text>\n<text id=\"mach\" x=\"${SX0}\" y=\"362\" fill=\"#d6d6d6\" font-size=\"17\" font-weight=\"700\"></text>\n</g>`;\n  const g = (id) => svg.querySelector('#' + id), el = {};\n  ['hz', 'hzl', 'rp', 'st', 'at', 'sb', 'ab', 'vn', 'vb', 'hd', 'hb', 's10', 'sdr', 'a100', 'adr', 'gs', 'mach', 'ra', 'f0', 'f1', 'f2', 'glsc', 'lcsc', 'gsd', 'lcd'].forEach((id) => { el[id] = g(id); });\n  const p3 = (n) => String(Math.round(n) % 360).padStart(3, '0'), w180 = (d) => ((d + 540) % 360) - 180;\n  const clampY = (y) => Math.max(TY0 + 10, Math.min(TY1 - 10, y));\n  function spdTape(v) {\n    let s = ''; const half = HALF / SPPU;\n    for (let t = Math.ceil((v - half) / 10) * 10; t <= v + half; t += 10) {\n      if (t < 0) continue;\n      const y = CY - (t - v) * SPPU, major = t % 20 === 0;\n      s += `<line x1=\"${SX1}\" x2=\"${SX1 - (major ? 14 : 8)}\" y1=\"${y}\" y2=\"${y}\" stroke=\"${INK}\" stroke-width=\"2\"/>`;\n      if (major) s += `<text x=\"${SX0 + 10}\" y=\"${y + 7}\" fill=\"#fff\" font-size=\"20\" font-weight=\"700\">${t}</text>`;\n    }\n    return s;\n  }\n  function altTape(v) {\n    let s = ''; const half = HALF / APPU;\n    for (let t = Math.ceil((v - half) / 100) * 100; t <= v + half; t += 100) {\n      const y = CY - (t - v) * APPU, major = t % 200 === 0;\n      s += `<line x1=\"${AX0}\" x2=\"${AX0 + (major ? 14 : 8)}\" y1=\"${y}\" y2=\"${y}\" stroke=\"${INK}\" stroke-width=\"2\"/>`;\n      if (major) s += `<text x=\"${AX1 - 8}\" y=\"${y + 7}\" text-anchor=\"end\" fill=\"#fff\" font-size=\"20\" font-weight=\"700\">${t}</text>`;\n    }\n    return s;\n  }\n  // Rolling digits in the readout boxes: higher values are on top, like on a tape\n  function spdDrum(v) {\n    const x = Math.max(0, v), tens = Math.floor(x / 10), f = x - tens * 10, n0 = Math.floor(f); let s = '';\n    for (let n = n0 - 1; n <= n0 + 2; n++) s += `<text x=\"124\" y=\"${CY + 11 - (n - f) * 30}\">${((n % 10) + 10) % 10}</text>`;\n    return [tens, s];\n  }\n  function altDrum(v) {\n    const x = Math.max(0, v), h = Math.floor(x / 100), f = x - h * 100, k0 = Math.floor(f / 20); let s = '';\n    for (let k = k0 - 1; k <= k0 + 2; k++) s += `<text x=\"655\" y=\"${CY + 9 - (k * 20 - f) * 1.3}\">${String(((k * 20) % 100 + 100) % 100).padStart(2, '0')}</text>`;\n    return [h, s];\n  }\n  function drawFma(s, ap) {\n    const on = ap.on === true, ln = s.lnav || {};\n    let c0 = '', c1 = '', c2 = '';\n    if (on) { c0 = ap.alt != null && Math.abs(s.alt - ap.alt) <= 150 ? 'ALT' : ap.vs != null ? 'V/S' : ''; c1 = ln.on ? 'NAV' : String(ap.mode || 'HDG'); c2 = 'AP'; }\n    if (s.paused) c2 = 'PAUSE';\n    el.f0.textContent = c0; el.f1.textContent = c1; el.f2.textContent = c2;\n  }\n  function drawPFD(s, now) {\n    const k = sgn(), pitch = s.pitch * k.p - pOff(), roll = s.roll * k.r, ap = s.ap || {}, dim = ap.on ? 1 : 0.6;\n    // Neus omhoog (+pitch) => horizon zakt; rechter vleugel omlaag (+roll) => horizon draait linksom\n    const tf = `translate(${CX},${CY}) rotate(${-roll}) translate(0,${pitch * PPD})`;\n    el.hz.setAttribute('transform', tf); el.hzl.setAttribute('transform', tf); el.rp.setAttribute('transform', `rotate(${-roll})`);\n    el.ra.textContent = s.hagl != null && s.hagl < 2500 && s.hagl > -50 ? Math.max(0, Math.round(s.hagl)) : '';\n    drawFma(s, ap);\n    // speed\n    el.st.innerHTML = spdTape(s.ias);\n    const sd = spdDrum(s.ias); el.s10.textContent = sd[0]; el.sdr.innerHTML = sd[1];\n    el.gs.textContent = Math.round(s.gs);\n    el.mach.textContent = typeof s.mach === 'number' && s.mach > 0.1 ? 'M ' + s.mach.toFixed(2).replace(/^0/, '') : '';\n    el.sb.innerHTML = ap.spd != null ? `<path d=\"M${SX1} ${clampY(CY - (ap.spd - s.ias) * SPPU)}l-14 -9v18z\" fill=\"none\" stroke=\"${MAG}\" stroke-width=\"3\" opacity=\"${dim}\"/>` : '';\n    // altitude\n    el.at.innerHTML = altTape(s.alt);\n    const ad = altDrum(s.alt); el.a100.textContent = ad[0] > 0 ? ad[0] : ''; el.adr.innerHTML = ad[1];\n    el.ab.innerHTML = ap.alt != null ? `<path d=\"M${AX0} ${clampY(CY - (ap.alt - s.alt) * APPU)}l14 -9v18z\" fill=\"none\" stroke=\"${MAG}\" stroke-width=\"3\" opacity=\"${dim}\"/>` : '';\n    // vertical speed\n    el.vn.setAttribute('d', `M750 ${CY}L716 ${CY + vsY(s.vs)}`);\n    el.vb.innerHTML = ap.on && ap.vs != null ? `<line x1=\"738\" x2=\"752\" y1=\"${CY + vsY(ap.vs)}\" y2=\"${CY + vsY(ap.vs)}\" stroke=\"${MAG}\" stroke-width=\"3.5\"/>` : '';\n    // kompasboog\n    const h = ((s.hdg % 360) + 360) % 360; let r = '';\n    for (let t = Math.ceil((h - 50) / 5) * 5; t <= h + 50; t += 5) {\n      const tt = ((t % 360) + 360) % 360, major = tt % 10 === 0;\n      r += `<g transform=\"rotate(${t - h} ${CX} ${RY})\"><line x1=\"${CX}\" x2=\"${CX}\" y1=\"${RY - RR}\" y2=\"${RY - RR + (major ? 14 : 8)}\" stroke=\"${INK}\" stroke-width=\"2\"/>`\n        + (major ? `<text x=\"${CX}\" y=\"${RY - RR + 38}\" text-anchor=\"middle\" fill=\"#fff\" font-size=\"20\" font-weight=\"700\">${String(tt / 10).padStart(2, '0')}</text>` : '') + '</g>';\n    }\n    el.hd.innerHTML = r;\n    const nv = s.nav, ln = s.lnav, rot = (d) => `rotate(${Math.max(-44, Math.min(44, w180(d)))} ${CX} ${RY})`; let b = '';\n    if (ap.hdg != null) b += `<path transform=\"${rot(ap.hdg - h)}\" d=\"M${CX - 10} ${RY - RR + 2}V${RY - RR - 12}H${CX + 10}V${RY - RR + 2}\" fill=\"none\" stroke=\"${MAG}\" stroke-width=\"3\" opacity=\"${dim}\"/>`;\n    // Direction to the selected waypoint, or the ILS course if there is a localizer\n    let tgt = null;\n    if (selIdx >= 0 && plan[selIdx]) tgt = brgTo(s.lat, s.lon, plan[selIdx].lat, plan[selIdx].lon);\n    else if (ln && ln.on && ln.brg != null) tgt = ln.brg;\n    else if (nv && nv.loc != null && nv.crs != null) tgt = nv.crs;\n    else if (nv && nv.brg != null) tgt = nv.brg;\n    if (tgt != null) b += `<path transform=\"${rot(tgt - h)}\" d=\"${dia(CX, RY - RR + 18, 7, 10)}\" fill=\"${MAG}\"/>`;\n    el.hb.innerHTML = b;\n    // ILS deviations: 1 dot = 1.25\u00b0 (localizer) resp. 0.35\u00b0 (glidepath); diamond up = you are below the path\n    const hasLoc = !!(nv && nv.loc != null), hasGs = !!(nv && nv.gs != null);\n    el.lcsc.setAttribute('display', 'inline'); el.glsc.setAttribute('display', 'inline'); // scales always visible, as in the photo\n    el.lcd.setAttribute('d', !hasLoc ? '' : dia(CX + Math.max(-2.1, Math.min(2.1, nv.loc / 1.25)) * 34, 297, 10, 6));\n    el.gsd.setAttribute('d', !hasGs ? '' : dia(565, CY + Math.max(-2.1, Math.min(2.1, nv.gs / 0.35)) * 30, 6, 10));\n  }\n  drawPFD({ ias: 0, gs: 0, alt: 0, hdg: 0, pitch: 0, roll: 0, vs: 0, ap: {} }, 0);\n\n  // ---------- PFD fullscreen (with pseudo-fullscreen for iPhone Safari) ----------\n  const fsb = $('#fsbtn'), isNativeFs = () => document.fullscreenElement || document.webkitFullscreenElement;\n  function setFs(on) {\n    document.body.classList.toggle('pfdfs', on);\n    try {\n      const el = $('#pfd');\n      if (on) {\n        const rq = el.requestFullscreen || el.webkitRequestFullscreen;\n        if (rq && !isNativeFs()) { const p = rq.call(el); if (p && p.catch) p.catch(() => {}); }\n        if (screen.orientation && screen.orientation.lock) screen.orientation.lock('landscape').catch(() => {});\n      } else {\n        if (isNativeFs()) (document.exitFullscreen || document.webkitExitFullscreen).call(document);\n        if (screen.orientation && screen.orientation.unlock) screen.orientation.unlock();\n      }\n    } catch (e) { /* the CSS variant (pseudo-fullscreen) keeps working */ }\n  }\n  fsb.onclick = () => setFs(!document.body.classList.contains('pfdfs'));\n  const onFsChange = () => { if (!isNativeFs() && document.body.classList.contains('pfdfs')) setFs(false); };\n  document.addEventListener('fullscreenchange', onFsChange); document.addEventListener('webkitfullscreenchange', onFsChange);\n\n  // ---------- autopilot tab (portrait) ----------\n  const APC = [\n    { k: 'hdg', name: 'HEADING', short: 'heading', unit: '\u00b0', cmd: 'set_hdg', steps: [-10, -1, 1, 10], min: 0, max: 359, wrap: true, fmt: (v) => String(Math.round(v) % 360).padStart(3, '0') },\n    { k: 'alt', name: 'ALTITUDE', short: 'altitude', unit: 'ft', cmd: 'set_alt', steps: [-1000, -100, 100, 1000], min: 0, max: 60000, fmt: (v) => Math.round(v) },\n    { k: 'spd', name: 'SPEED (IAS)', short: 'speed', unit: 'kt', cmd: 'set_spd', steps: [-10, -1, 1, 10], min: 60, max: 700, fmt: (v) => Math.round(v) },\n    { k: 'vs', name: 'VERTICAL SPEED', short: 'VS', unit: 'fpm', cmd: 'set_vs', steps: [-500, -100, 100, 500], min: -6000, max: 6000, fmt: (v) => (v > 0 ? '+' : '') + Math.round(v) },\n  ];\n  const sgnTxt = (d) => (d > 0 ? '+' : '\u2212') + Math.abs(d);\n  const apGrid = $('#apgrid'), dirty = {};\n  apGrid.innerHTML = APC.map((c) => `<div class=\"apc\"><div class=\"aph\"><span class=\"apl\">${c.name}</span><span class=\"apv\"><b id=\"v-${c.k}\">\u2014</b><small>${c.unit}</small></span></div>\n<div class=\"apr\">${c.steps.slice(0, 2).map((d) => `<button data-k=\"${c.k}\" data-d=\"${d}\">${sgnTxt(d)}</button>`).join('')}<input id=\"i-${c.k}\" data-k=\"${c.k}\" type=\"number\" inputmode=\"numeric\" step=\"1\">${c.steps.slice(2).map((d) => `<button data-k=\"${c.k}\" data-d=\"${d}\">${sgnTxt(d)}</button>`).join('')}</div>\n<button class=\"set\" data-k=\"${c.k}\" data-set=\"1\">Set ${c.short}</button></div>`).join('');\n  const apOf = (c) => (latestState() && latestState().ap && latestState().ap[c.k]);\n  const norm = (c, v) => (c.wrap ? ((Math.round(v) % 360) + 360) % 360 : Math.min(c.max, Math.max(c.min, Math.round(v))));\n\n  let cid = 0, msgT = null; const pend = new Map();\n  function say(txt, cls) {\n    const el = $('#apmsg'); el.textContent = txt; el.className = cls || '';\n    clearTimeout(msgT); msgT = setTimeout(() => { el.textContent = ''; el.className = ''; }, 7000);\n  }\n  function sendCmd(name, value, label, k) {\n    if (!canSend()) { say('Not connected: command not sent', 'bad'); return; }\n    const id = ++cid; pend.set(id, { name, label, k, t: performance.now() });\n    tr.send({ t: 'cmd', id, name, value }); say(label + '\u2026', '');\n  }\n  function onAck(m) {\n    const p = pend.get(m.id); if (!p) return; pend.delete(m.id);\n    if (m.ok) { say('\u2714 ' + p.label + (m.applied != null && typeof m.applied !== 'boolean' && p.name !== 'nav_direct' ? ' \u2192 ' + m.applied : ''), 'ok'); if (p.k) dirty[p.k] = false; }\n    else say('\u2716 ' + p.label + ': ' + (m.err || 'error'), 'bad');\n  }\n  setInterval(() => { const n = performance.now(); pend.forEach((p, id) => { if (n - p.t > CFG.ackMs) { pend.delete(id); say(p.label + ': no response from the sim', 'bad'); } }); }, 500);\n\n  apGrid.addEventListener('click', (e) => {\n    const b = e.target.closest('button'); if (!b) return;\n    const c = APC.find((x) => x.k === b.dataset.k), inp = $('#i-' + c.k);\n    if (b.dataset.set) {\n      const v = parseFloat(inp.value); if (!isFinite(v)) { say('Enter a number first', 'bad'); return; }\n      const val = norm(c, v); inp.value = val; sendCmd(c.cmd, val, c.short + ' ' + val, c.k);\n    } else {\n      let base = parseFloat(inp.value); if (!isFinite(base)) base = Number(apOf(c)) || 0;\n      inp.value = norm(c, base + Number(b.dataset.d)); dirty[c.k] = true;\n    }\n  });\n  apGrid.addEventListener('input', (e) => { if (e.target.dataset.k) dirty[e.target.dataset.k] = true; });\n  $('#aptog').onclick = () => { const s = latestState(), on = !!(s && s.ap && s.ap.on); sendCmd('ap_toggle', !on, 'autopilot ' + (on ? 'off' : 'on')); };\n  $('#pausebtn').onclick = () => { const s = latestState(), p = !!(s && s.paused); sendCmd('sim_pause', !p, p ? 'resuming sim' : 'pausing sim'); };\n  listEl.addEventListener('click', (e) => {\n    const row = e.target.closest('.fp'); if (!row || !plan[+row.dataset.i]) return;\n    const i = +row.dataset.i;\n    if (e.target.closest('button')) { selIdx = i; paintSel(); sendCmd('nav_direct', i, 'direct to ' + plan[i].n); }\n    else { selIdx = selIdx === i ? -1 : i; paintSel(); } // tap the row: select / deselect again\n  });\n  $('#lnavstop').onclick = () => sendCmd('nav_cancel', true, 'stopping direct');\n\n  function updateAp(s) {\n    const a = (s && s.ap) || {}, ok = !!s && canSend();\n    $('#ap').classList.toggle('dis', !ok);\n    $('#ap').querySelectorAll('button,input').forEach((el) => { el.disabled = !ok; });\n    const t = $('#aptog'); t.textContent = 'AUTOPILOT: ' + (a.on === true ? 'ON' : a.on === false ? 'OFF' : '\u2014'); t.className = a.on === true ? 'on' : 'off';\n    const pb = $('#pausebtn'), pz = !!(s && s.paused); pb.textContent = pz ? 'RESUME' : 'PAUSE'; pb.className = pz ? 'paused' : '';\n    // Always show what the sim really has; the input field follows the sim as long as you are not editing\n    for (const c of APC) {\n      const v = a[c.k], inp = $('#i-' + c.k);\n      $('#v-' + c.k).textContent = v == null ? '\u2014' : c.fmt(v);\n      if (!dirty[c.k] && document.activeElement !== inp && v != null) inp.value = Math.round(v);\n    }\n    // flight plan: distance/bearing to each point, direct-to status\n    const ln = (s && s.lnav) || {}, lt = $('#lnavtxt'), stop = $('#lnavstop');\n    stop.hidden = !ln.on;\n    if (ln.on) lt.textContent = `Direct \u2192 ${ln.n || '?'} \u00b7 ${ln.brg != null ? p3(ln.brg) + '\u00b0' : ''} \u00b7 ${ln.dist != null ? ln.dist + ' NM' : ''}` + (a.on === false ? ' \u00b7 AP is off!' : '');\n    else lt.textContent = ln.done ? 'Last waypoint reached' : '';\n    if (s) listEl.querySelectorAll('.fp').forEach((el, i) => {\n      const p = plan[i]; if (!p) return;\n      el.querySelector('.mid').textContent = `${p.alt != null ? Math.round(p.alt) + ' ft \u00b7 ' : ''}${p3(brgTo(s.lat, s.lon, p.lat, p.lon))}\u00b0 \u00b7 ${distNm(s.lat, s.lon, p.lat, p.lon).toFixed(1)} NM`;\n    });\n  }\n\n  // ---------- render-lus ----------\n  let lastAp = 0;\n  (function frame(now) {\n    let s = sample();\n    if (s) s.ias = smoothIas(s.ias, now);\n    if (tab === 'pfd') { if (s) drawPFD(s, now); }\n    else if (tab === 'ap' && now - lastAp > 200) { lastAp = now; updateAp(latestState()); }\n    requestAnimationFrame(frame);\n  })(0);\n\n  // ---------- Wake Lock ----------\n  let wl = null;\n  async function lock() { try { if ('wakeLock' in navigator && document.visibilityState === 'visible' && (!wl || wl.released)) wl = await navigator.wakeLock.request('screen'); } catch (e) { /* geweigerd */ } }\n  document.addEventListener('visibilitychange', lock); document.addEventListener('click', lock); lock();\n\n  // (no service worker in the single-file version)\n  readHash(); go(); applyOrient();\n  if (!LS.peer) $('#gear').click();\n})();\n</script>\n</body></html>\n";
  function downloadPwa() {
    const a = document.createElement('a');
    a.href = URL.createObjectURL(new Blob([PWA_HTML], { type: 'text/html' }));
    a.download = 'index.html'; document.body.appendChild(a); a.click(); a.remove();
  }

  // ===== UI: one black button in the bottom menu bar of GeoFS, with a panel behind it =====
  const UI = (() => {
    const CSS = '#gc-btn{box-sizing:border-box;width:28px;height:28px;padding:0;margin:0 4px;background:#000;border:0;border-radius:4px;cursor:pointer;vertical-align:middle;display:inline-flex;align-items:center;justify-content:center;opacity:.55}'
      + '#gc-btn.on{opacity:1}#gc-btn svg{width:16px;height:16px;fill:#fff;display:block}'
      + '#gc-btn.gc-float{position:fixed;left:8px;bottom:8px;z-index:2147483646}'
      + '#gc-panel{position:fixed;left:8px;bottom:56px;z-index:2147483647;width:300px;max-height:80vh;overflow:auto;background:#111823;color:#e6edf3;border:1px solid #2c3b52;border-radius:10px;padding:12px;font:13px system-ui,sans-serif;display:none;box-shadow:0 6px 24px rgba(0,0,0,.5)}'
      + '#gc-panel h4{margin:0 0 8px;font-size:14px}#gc-panel .r{display:flex;align-items:center;gap:6px;margin:6px 0}#gc-panel .r b{width:46px;color:#8b98a9;font-weight:600}'
      + '#gc-panel code{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;background:#0a0e14;border-radius:5px;padding:5px 6px;font-size:11px;user-select:all}'
      + '#gc-panel button{background:#1b2636;color:#e6edf3;border:1px solid #2c3b52;border-radius:6px;padding:5px 9px;font:inherit;cursor:pointer}#gc-panel button:hover{background:#243248}'
      + '#gc-panel .acts{display:flex;flex-wrap:wrap;gap:6px;margin-top:10px}#gc-panel #gc-e{color:#f99;margin-top:6px}#gc-panel #gc-n{color:#9cf;margin-top:6px}#gc-qr{background:#fff;padding:8px;border-radius:6px;margin-top:8px;text-align:center}';
    const st = document.createElement('style'); st.textContent = CSS; document.head.appendChild(st);

    const btn = document.createElement('button'); btn.id = 'gc-btn'; btn.title = 'GeoFS Companion'; btn.setAttribute('aria-label', 'GeoFS Companion'); btn.innerHTML = '<svg viewBox="0 0 24 24"><path d="M12 2c.8 0 1.5.9 1.5 2.2V9l8.5 5v2.2l-8.5-2.4v4.4l2.2 1.7V22L12 21l-3.7 1v-1.9l2.2-1.7v-4.4L2 16.2V14l8.5-5V4.2C10.5 2.9 11.2 2 12 2z"/></svg>';
    const panel = document.createElement('div'); panel.id = 'gc-panel';
    panel.innerHTML = '<h4>GeoFS Companion <span id="gc-s" style="font-weight:400;color:#8b98a9">starting…</span></h4>'
      + '<div class="r"><b>Peer</b><code id="gc-peer"></code><button data-copy="peer">Copy</button></div>'
      + '<div class="r"><b>Token</b><code id="gc-token"></code><button data-copy="token">Copy</button></div>'
      + '<div class="r"><b>Link</b><code id="gc-link"></code><button data-copy="link">Copy</button></div>'
      + '<div id="gc-qr"></div>'
      + '<div class="acts"><button id="gc-d">Diagnose</button><button id="gc-p">Download PWA</button><button id="gc-r">Reset pairing</button><button id="gc-x">Close</button></div>'
      + '<div id="gc-n"></div><div id="gc-e"></div>';
    document.body.appendChild(panel);
    const $ = (s) => panel.querySelector(s);

    const link = () => CONFIG.PWA_URL + '#peer=' + Host.pairing.id + '&token=' + Host.pairing.token;
    const values = () => ({ peer: Host.pairing.id, token: Host.pairing.token, link: link() });
    function fill() {
      const v = values(); $('#gc-peer').textContent = v.peer; $('#gc-token').textContent = v.token; $('#gc-link').textContent = v.link;
      try { const q = qrcode(0, 'M'); q.addData(v.link); q.make(); $('#gc-qr').innerHTML = q.createImgTag(4, 8); } catch (e) { $('#gc-qr').textContent = 'QR not available'; }
    }
    async function copy(text) {
      try { await navigator.clipboard.writeText(text); return true; } catch (e) {
        const ta = document.createElement('textarea'); ta.value = text; ta.style.cssText = 'position:fixed;opacity:0'; document.body.appendChild(ta); ta.select();
        let ok = false; try { ok = document.execCommand('copy'); } catch (e2) { /* ignore */ } ta.remove(); return ok;
      }
    }
    panel.addEventListener('click', async (e) => {
      const b = e.target.closest('button[data-copy]'); if (!b) return;
      const ok = await copy(values()[b.dataset.copy]); const t = b.textContent; b.textContent = ok ? 'Copied ✓' : 'Failed'; setTimeout(() => { b.textContent = t; }, 1500);
    });
    const open = () => { fill(); panel.style.display = 'block'; };
    const toggle = () => { if (panel.style.display === 'block') panel.style.display = 'none'; else open(); };
    function reset() { if (confirm('Reset pairing? The phone will have to pair again.')) { Host.reset(); fill(); } }
    btn.onclick = toggle; $('#gc-x').onclick = () => { panel.style.display = 'none'; };
    $('#gc-d').onclick = diagnose; $('#gc-p').onclick = downloadPwa; $('#gc-r').onclick = reset;
    GM_registerMenuCommand('Companion panel', toggle);
    GM_registerMenuCommand('Reset pairing', reset);
    GM_registerMenuCommand('Diagnose (console)', diagnose);
    GM_registerMenuCommand('Download PWA (index.html)', downloadPwa);

    // Put the button in the white GeoFS menu bar (GeoFS only builds it after loading); otherwise a floating button.
    function place() {
      if (btn.isConnected) return;
      const bar = document.querySelector('.geofs-ui-bottom');
      if (bar) { btn.classList.remove('gc-float'); bar.appendChild(btn); }
      else if (!btn.isConnected && Date.now() - t0 > 15000) { btn.classList.add('gc-float'); document.body.appendChild(btn); }
    }
    const t0 = Date.now(); place(); setInterval(place, 1500);

    let nt = null;
    return {
      status: (s) => { $('#gc-s').textContent = s; btn.classList.toggle('on', /connected/.test(s) && !/waiting/.test(s)); },
      err: (s) => { $('#gc-e').textContent = s; },
      note: (s) => { $('#gc-n').textContent = s; panel.style.display = 'block'; clearTimeout(nt); nt = setTimeout(() => { $('#gc-n').textContent = ''; }, 14000); },
    };
  })();

  // ===== MAIN =====
  // Timer in a Worker: less affected by throttling in background tabs. Fallback: setInterval.
  function everyMs(fn, ms) {
    let fell = false; const fb = () => { if (!fell) { fell = true; setInterval(fn, ms); } };
    try {
      const w = new Worker(URL.createObjectURL(new Blob(['setInterval(()=>postMessage(0),' + ms + ')'])));
      w.onmessage = fn; w.onerror = () => { w.terminate(); fb(); };
    } catch (e) { fb(); }
  }
  let lastErr = '', tickN = 0, planSig = null, planEpoch = -1;
  everyMs(() => {
    try {
      const s = Adapter.readState();
      if (lastErr) { lastErr = ''; UI.err(''); }
      let nav = null; try { nav = Nav.info(s); } catch (e) { /* navaid unknown: no nav data */ }
      if (++tickN % CONFIG.RATE_HZ === 0) { // once per second
        Nav.tick(s);
        try {
          const plan = Adapter.flightPlan() || [], sig = JSON.stringify(plan);
          if (Host.connected && (sig !== planSig || Host.epoch !== planEpoch)) { Host.send({ t: 'plan', wps: plan }); planSig = sig; planEpoch = Host.epoch; }
        } catch (e) { /* no flight plan */ }
      }
      if (Host.connected) Host.send(Object.assign({ t: 'state', ts: Date.now() }, s, { nav, lnav: Nav.status() }));
    } catch (e) {
      if (e.message !== lastErr) { lastErr = e.message; UI.err(e.message); console.warn('[GeoFS Companion]', e.message); }
    }
  }, Math.round(1000 / CONFIG.RATE_HZ));
  setInterval(() => Host.send({ t: 'ping', ts: Date.now() }), 2000);
  Host.onStatus(UI.status);
  Host.start();
  console.log('[GeoFS Companion] started. Peer ID:', Host.pairing.id);
})();
