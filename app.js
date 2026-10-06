/* Pli — messagerie privée sans réseau
   Chiffrement : ECDH P-256 + HKDF + AES-GCM (WebCrypto). Aucune donnée ne quitte l'appareil hors des plis. */
(() => {
'use strict';
const KEY = 'pli.v1', FAILKEY = 'pli.fail';
const $ = s => document.querySelector(s);
const enc = new TextEncoder(), dec = new TextDecoder();
const esc = s => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const rand = n => crypto.getRandomValues(new Uint8Array(n));
const uid = () => [...rand(9)].map(b => b.toString(16).padStart(2,'0')).join('');
const embedded = (() => { try { return window.self !== window.top; } catch(e) { return true; } })();
const canShare = !embedded && !!navigator.share;
const coarse = matchMedia('(pointer:coarse)').matches;
const isNarrow = () => matchMedia('(max-width:760px)').matches;
const HAS_QR = typeof window.qrcode === 'function';
const HAS_SCAN = typeof window.jsQR === 'function';
const RTC_OK = !embedded && typeof window.RTCPeerConnection === 'function';
const QR_MAX = 1400;

/* capacité de téléchargement quand la page tourne dans la visionneuse */
let dlCap = null;
try { if (window.claude && typeof window.claude.use === 'function') window.claude.use('downloads').then(d => { dlCap = d; }).catch(() => {}); } catch(e) {}
const canSave = () => !embedded || !!dlCap;

/* ---------- encodage ---------- */
function b64u(buf){ const b = buf instanceof Uint8Array ? buf : new Uint8Array(buf); let s=''; for (let i=0;i<b.length;i++) s += String.fromCharCode(b[i]); return btoa(s).replace(/\+/g,'-').replace(/\//g,'_').replace(/=+$/,''); }
function unb64u(str){ str = str.replace(/-/g,'+').replace(/_/g,'/'); while (str.length % 4) str += '='; const s = atob(str); const b = new Uint8Array(s.length); for (let i=0;i<s.length;i++) b[i] = s.charCodeAt(i); return b; }
const packJSON = o => b64u(enc.encode(JSON.stringify(o)));
const unpackJSON = s => JSON.parse(dec.decode(unb64u(s)));
async function zpack(o){
  const str = JSON.stringify(o);
  if (typeof CompressionStream !== 'function') return 'r' + b64u(enc.encode(str));
  const st = new Blob([str]).stream().pipeThrough(new CompressionStream('deflate-raw'));
  return 'z' + b64u(await new Response(st).arrayBuffer());
}
async function zunpack(s){
  const kind = s[0], b = unb64u(s.slice(1));
  if (kind === 'r') return JSON.parse(dec.decode(b));
  if (kind !== 'z' || typeof DecompressionStream !== 'function') throw new Error('damaged');
  const st = new Blob([b]).stream().pipeThrough(new DecompressionStream('deflate-raw'));
  return JSON.parse(await new Response(st).text());
}

/* ---------- chiffrement : ECDH P-256 -> HKDF-SHA256 -> AES-GCM 256 ---------- */
const EC = {name:'ECDH', namedCurve:'P-256'};
async function newKeys(){
  const kp = await crypto.subtle.generateKey(EC, true, ['deriveBits']);
  const priv = await crypto.subtle.exportKey('jwk', kp.privateKey);
  const pubJ = await crypto.subtle.exportKey('jwk', kp.publicKey);
  return { priv, pub: {x:pubJ.x, y:pubJ.y} };
}
const jwkPub = p => ({kty:'EC', crv:'P-256', x:p.x, y:p.y, ext:true});
async function fingerprint(p){
  const h = await crypto.subtle.digest('SHA-256', enc.encode(p.x + '.' + p.y));
  return [...new Uint8Array(h).slice(0,10)].map(b => b.toString(16).padStart(2,'0')).join('').toUpperCase();
}
const fmtFp = fp => (fp || '').match(/.{1,4}/g).join(' ');
const keyCache = new Map();
async function sharedKey(myPriv, theirPub, myFp, theirFp){
  const id = myFp + '|' + theirFp;
  if (keyCache.has(id)) return keyCache.get(id);
  const priv = await crypto.subtle.importKey('jwk', myPriv, EC, false, ['deriveBits']);
  const pub = await crypto.subtle.importKey('jwk', jwkPub(theirPub), EC, false, []);
  const bits = await crypto.subtle.deriveBits({name:'ECDH', public:pub}, priv, 256);
  const hk = await crypto.subtle.importKey('raw', bits, 'HKDF', false, ['deriveKey']);
  const k = await crypto.subtle.deriveKey(
    {name:'HKDF', hash:'SHA-256', salt:enc.encode([myFp, theirFp].sort().join('|')), info:enc.encode('pli/v1')},
    hk, {name:'AES-GCM', length:256}, false, ['encrypt','decrypt']);
  keyCache.set(id, k); return k;
}
async function seal(from, toPub, toFp, payload){
  const k = await sharedKey(from.priv, toPub, from.fp, toFp);
  const iv = rand(12);
  const c = await crypto.subtle.encrypt({name:'AES-GCM', iv, additionalData:enc.encode(from.fp + '>' + toFp)}, k, enc.encode(JSON.stringify(payload)));
  return 'PLI1.' + packJSON({v:1, k:from.pub, t:toFp, i:b64u(iv), c:b64u(c)});
}
async function openPli(code, me){
  let o; try { o = unpackJSON(code.slice(5)); } catch(e) { throw new Error('damaged'); }
  if (!o || !o.k || !o.k.x || !o.t) throw new Error('damaged');
  if (o.t !== me.fp) throw new Error('not-for-me');
  const fromFp = await fingerprint(o.k);
  const k = await sharedKey(me.priv, o.k, me.fp, fromFp);
  let pt;
  try { pt = await crypto.subtle.decrypt({name:'AES-GCM', iv:unb64u(o.i), additionalData:enc.encode(fromFp + '>' + me.fp)}, k, unb64u(o.c)); }
  catch(e) { throw new Error('damaged'); }
  return { fromFp, fromPub:{x:o.k.x, y:o.k.y}, payload: JSON.parse(dec.decode(pt)) };
}
const cardCode = me => 'CARTE1.' + packJSON({v:1, n:me.name, k:me.pub});

/* ---------- code de verrouillage : PBKDF2-SHA256 -> AES-GCM 256 ---------- */
const PIN_ITER = 310000;
async function pinKey(pin, salt, iter){
  const base = await crypto.subtle.importKey('raw', enc.encode(pin), 'PBKDF2', false, ['deriveKey']);
  return crypto.subtle.deriveKey({name:'PBKDF2', hash:'SHA-256', salt, iterations:iter}, base, {name:'AES-GCM', length:256}, false, ['encrypt','decrypt']);
}

/* ---------- état et stockage local ---------- */
const emptyState = () => ({ me:null, demo:null, contacts:{}, msgs:{}, drafts:{}, settings:{autoLock:5} });
let S = emptyState();
let current = null;
let lockMeta = null, lockKey = null;
const store = {
  ok: (() => { try { localStorage.setItem('pli.t','1'); localStorage.removeItem('pli.t'); return true; } catch(e) { return false; } })(),
  read(){ if (!this.ok) return null; try { const r = localStorage.getItem(KEY); return r ? JSON.parse(r) : null; } catch(e) { return null; } },
  write(str){ if (!this.ok) return; try { localStorage.setItem(KEY, str); } catch(e) { this.ok = false; renderFoot(); } },
  wipe(){ try { localStorage.removeItem(KEY); localStorage.removeItem(FAILKEY); } catch(e) {} }
};
let saveTimer = null, saveChain = Promise.resolve();
function save(){ if (!S.me) return; clearTimeout(saveTimer); saveTimer = setTimeout(flushSave, 40); }
function flushSave(){
  clearTimeout(saveTimer);
  if (!S.me) return saveChain;
  const snap = JSON.stringify(S), meta = lockMeta, key = lockKey;
  saveChain = saveChain.then(async () => {
    if (meta && key) {
      const iv = rand(12);
      const c = await crypto.subtle.encrypt({name:'AES-GCM', iv}, key, enc.encode(snap));
      store.write(JSON.stringify({v:2, lock:meta, iv:b64u(iv), c:b64u(c)}));
    } else if (!meta) store.write(snap);
  }).catch(() => {});
  return saveChain;
}
addEventListener('pagehide', () => { if (S.me && !lockMeta) store.write(JSON.stringify(S)); });

/* ---------- utilitaires d'affichage ---------- */
const hue = fp => parseInt((fp || '00').slice(0,4), 16) % 360;
const initials = n => (n || '?').replace(/\(.*?\)/g,'').trim().split(/\s+/).filter(w => /\p{L}/u.test(w)).slice(0,2).map(w => w.match(/\p{L}/u)[0]).join('').toUpperCase() || '?';
function avatar(el, c){ el.textContent = initials(c.name); el.style.setProperty('--h', hue(c.fp)); }
const tFmt = new Intl.DateTimeFormat('fr-FR', {hour:'2-digit', minute:'2-digit'});
const dFmt = new Intl.DateTimeFormat('fr-FR', {weekday:'long', day:'numeric', month:'long'});
const sFmt = new Intl.DateTimeFormat('fr-FR', {day:'2-digit', month:'2-digit'});
function dayLabel(t){
  const d = new Date(t), n = new Date(); const sd = (a,b) => a.toDateString() === b.toDateString();
  if (sd(d,n)) return "Aujourd'hui"; const y = new Date(n); y.setDate(n.getDate()-1);
  if (sd(d,y)) return 'Hier'; return dFmt.format(d);
}
function shortTime(t){ const d = new Date(t); return d.toDateString() === new Date().toDateString() ? tFmt.format(d) : sFmt.format(d); }
const fmtBytes = n => n < 1024 ? n + ' octets' : (n/1024).toLocaleString('fr-FR', {maximumFractionDigits:1}) + ' Ko';
let toastT;
function toast(msg, ms = 3200){ const t = $('#toast'); t.textContent = msg; t.hidden = false; clearTimeout(toastT); toastT = setTimeout(() => t.hidden = true, ms); }
const plural = (n, one, many) => n + ' ' + (n > 1 ? many : one);

/* ---------- QR : affichage ---------- */
function qrSvg(text, ecl){
  if (!HAS_QR) return '';
  try {
    const q = qrcode(0, ecl || 'M'); q.addData(text, 'Byte'); q.make();
    const n = q.getModuleCount(), m = 4, size = n + m*2; let d = '';
    for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) if (q.isDark(r, c)) d += `M${c+m} ${r+m}h1v1h-1z`;
    return `<figure class="qr-wrap"><svg class="qr" viewBox="0 0 ${size} ${size}" role="img" aria-label="QR code"><rect width="${size}" height="${size}" fill="var(--qr-bg)"/><path d="${d}" fill="var(--qr-fg)" shape-rendering="crispEdges"/></svg></figure>`;
  } catch(e) { return ''; }
}
function qrOrNote(text, ecl, what){
  if (!HAS_QR) return '<p class="note">Les QR codes ne sont pas disponibles dans cette version. Utilisez le code ci-dessous.</p>';
  if (text.length > QR_MAX) return `<p class="note">${what} est trop long pour un QR lisible (${text.length} caractères). Utilisez le partage, le fichier ou le copier-coller.</p>`;
  return qrSvg(text, ecl) || '<p class="note">QR impossible à générer pour ce contenu. Utilisez le code ci-dessous.</p>';
}

/* ---------- QR : lecture (caméra ou photo) ---------- */
function scannerHTML(label){
  if (!HAS_SCAN) return '<p class="note">La lecture des QR codes n\'est pas disponible dans cette version. Collez le code ou choisissez le fichier.</p>';
  return `<div class="scanbox">
    <div class="scan" hidden><video playsinline muted></video><span class="scan-frame"></span></div>
    <p class="note scan-state" aria-live="polite"></p>
    <div class="actions">
      <button class="btn primary" type="button" data-scan="cam"><svg><use href="#i-qr"/></svg>${label || 'Scanner avec la caméra'}</button>
      <label class="btn label-btn"><svg><use href="#i-photo"/></svg>Photo du QR<input type="file" accept="image/*" data-scan="photo" hidden></label>
    </div></div>`;
}
async function decodeImageFile(file){
  let src;
  try { src = await createImageBitmap(file); }
  catch(e) {
    src = await new Promise((res, rej) => { const im = new Image(); im.onload = () => res(im); im.onerror = rej; im.src = URL.createObjectURL(file); });
  }
  const W = src.width, H = src.height, cv = document.createElement('canvas'), cx = cv.getContext('2d', {willReadFrequently:true});
  for (const max of [1000, 1600, 700, 2200, 480]) {
    const s = Math.min(1, max / Math.max(W, H)); cv.width = Math.max(1, W*s|0); cv.height = Math.max(1, H*s|0);
    cx.drawImage(src, 0, 0, cv.width, cv.height);
    const img = cx.getImageData(0, 0, cv.width, cv.height);
    const r = jsQR(img.data, img.width, img.height, {inversionAttempts:'attemptBoth'});
    if (r && r.data) return r.data;
    if (s === 1) break;
  }
  return null;
}
function wireScanner(root, onText){
  const box = root.querySelector('.scanbox'); if (!box) return () => {};
  const wrap = box.querySelector('.scan'), video = box.querySelector('video'), state = box.querySelector('.scan-state');
  const camBtn = box.querySelector('[data-scan=cam]'), photo = box.querySelector('[data-scan=photo]');
  const cv = document.createElement('canvas'), cx = cv.getContext('2d', {willReadFrequently:true});
  let stream = null, raf = 0, live = false;
  const stop = () => { live = false; cancelAnimationFrame(raf); if (stream) stream.getTracks().forEach(t => t.stop()); stream = null; wrap.hidden = true; camBtn.hidden = false; };
  camBtn.onclick = async () => {
    if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) { state.textContent = "La caméra n'est pas accessible ici. Prenez le QR en photo avec « Photo du QR »."; return; }
    state.textContent = 'Ouverture de la caméra…';
    try { stream = await navigator.mediaDevices.getUserMedia({video:{facingMode:{ideal:'environment'}}, audio:false}); }
    catch(e) { state.textContent = "La caméra n'est pas accessible ici. Prenez le QR en photo avec « Photo du QR »."; return; }
    video.srcObject = stream; try { await video.play(); } catch(e) {}
    wrap.hidden = false; camBtn.hidden = true; live = true; state.textContent = 'Placez le QR dans le cadre.';
    let last = 0;
    const tick = t => {
      if (!live) return; raf = requestAnimationFrame(tick);
      if (t - last < 110 || video.readyState < 2 || !video.videoWidth) return; last = t;
      const w = video.videoWidth, h = video.videoHeight, s = Math.min(1, 800 / Math.max(w, h));
      cv.width = w*s|0; cv.height = h*s|0; cx.drawImage(video, 0, 0, cv.width, cv.height);
      const img = cx.getImageData(0, 0, cv.width, cv.height);
      const r = jsQR(img.data, img.width, img.height, {inversionAttempts:'dontInvert'});
      if (r && r.data) { stop(); try { navigator.vibrate && navigator.vibrate(40); } catch(e) {} state.textContent = 'QR lu.'; onText(r.data, state); }
    };
    raf = requestAnimationFrame(tick);
  };
  photo.onchange = async () => {
    const f = photo.files && photo.files[0]; photo.value = ''; if (!f) return;
    state.textContent = 'Lecture de la photo…';
    let txt = null; try { txt = await decodeImageFile(f); } catch(e) {}
    if (txt) { state.textContent = 'QR lu.'; onText(txt, state); }
    else state.textContent = 'Aucun QR lisible sur cette photo. Cadrez le QR en entier, de plus près, sans reflet.';
  };
  return stop;
}

/* ---------- rendu ---------- */
function renderMe(){
  $('#meName').textContent = S.me.name; $('#meFp').textContent = fmtFp(S.me.fp).slice(0,14) + '…';
  avatar($('#meAv'), S.me);
  $('#lockBtn').hidden = !lockMeta;
}
function renderFoot(){
  const f = $('#storeNote');
  if (!store.ok) { f.className = 'side-foot warn'; f.textContent = "Stockage bloqué dans ce navigateur : tout sera effacé à la fermeture de la page."; return; }
  f.className = 'side-foot';
  if (S.me && !S.settings.lastBackup && Object.values(S.contacts).some(c => !c.demo)) {
    f.className = 'side-foot warn';
    f.innerHTML = 'Votre compte n\'est pas sauvegardé. <button type="button" class="linkish" id="footBak">Sauvegarder</button>';
    f.querySelector('#footBak').onclick = sheetBackup;
    return;
  }
  f.textContent = lockMeta ? 'Chiffré de bout en bout. Données protégées par votre code sur cet appareil.' : 'Chiffré de bout en bout. Clés et messages restent sur cet appareil.';
}
function lastOf(fp){ const l = S.msgs[fp] || []; return l[l.length-1]; }
function renderList(){
  renderFoot();
  const ul = $('#list');
  const cs = Object.values(S.contacts).sort((a,b) => ((lastOf(b.fp)||{}).t || b.added) - ((lastOf(a.fp)||{}).t || a.added));
  if (!cs.length) { ul.innerHTML = '<li class="sys" style="padding:20px 8px">Aucun contact. Scannez la carte d\'un proche avec « Ajouter », ou ouvrez un pli reçu.</li>'; return; }
  ul.innerHTML = cs.map(c => {
    const last = lastOf(c.fp); const pend = (S.msgs[c.fp]||[]).filter(m => m.st === 'pending').length;
    const isLive = isLiveOpen(c.fp);
    const prev = last ? (last.dir === 'out' ? 'Vous : ' : '') + last.b.replace(/\s+/g,' ') : 'Nouveau contact';
    return `<li><button type="button" data-fp="${c.fp}" aria-current="${c.fp === current}">
      <span class="av-wrap"><span class="av" style="--h:${hue(c.fp)}">${esc(initials(c.name))}</span>${isLive ? '<span class="dot-live" title="En direct"></span>' : ''}</span>
      <span class="c-main"><span class="c-top"><span class="c-name">${esc(c.name)}</span><span class="c-time">${last ? shortTime(last.t) : ''}</span></span>
      <span class="c-bot"><span class="c-prev">${esc(prev)}</span>${pend && !isLive ? `<span class="badge pend">${pend} à remettre</span>` : ''}${c.unread ? `<span class="badge unread">${c.unread}</span>` : ''}</span></span>
    </button></li>`;
  }).join('');
}
function renderChat(){
  const c = current && S.contacts[current];
  $('#emptyChat').hidden = !!c;
  for (const id of ['#chatHead','#thread','#composer']) $(id).hidden = !c;
  if (!c) { $('#pendBar').hidden = true; return; }
  avatar($('#cAv'), c); $('#cName').textContent = c.name;
  const L = live.get(c.fp), isLive = isLiveOpen(c.fp);
  const tr = $('#cTrust');
  if (isLive) { tr.className = 'trust live'; tr.textContent = L.authed ? 'En direct sur le Wi-Fi local' : 'Connexion directe…'; }
  else if (c.verified) { tr.className = 'trust ok'; tr.innerHTML = '<svg width="13" height="13"><use href="#i-lock"/></svg>Empreinte vérifiée'; }
  else { tr.className = 'trust no'; tr.textContent = c.demo ? 'Contact simulé sur cet appareil' : 'Empreinte non vérifiée'; }
  const lb = $('#liveBtn'); lb.hidden = !!c.demo; lb.classList.toggle('on', isLive);
  lb.setAttribute('aria-label', isLive ? 'Couper la discussion en direct' : 'Démarrer une discussion en direct');
  lb.querySelector('span').textContent = isLive ? 'En direct' : 'Direct';
  const list = S.msgs[c.fp] || [];
  let html = '', lastDay = '';
  if (!list.length) html = `<p class="sys">Aucun message. Ce que vous écrivez reste ici, scellé, jusqu'à ce que vous prépariez un pli pour ${esc(c.name)} ou que vous passiez en direct.</p>`;
  for (const m of list) {
    const dl = dayLabel(m.t); if (dl !== lastDay) { html += `<div class="day">${dl}</div>`; lastDay = dl; }
    const st = m.dir === 'out' ? (m.st === 'pending' ? `<span class="st-pend">${isLive ? 'envoi…' : 'à remettre'}</span>` : '<span>✓ remis</span>') : '';
    html += `<div class="msg ${m.dir}${m.st === 'pending' ? ' pending' : ''}">${esc(m.b)}<div class="meta"><span>${tFmt.format(new Date(m.t))}</span>${st}</div></div>`;
  }
  const th = $('#thread'); th.innerHTML = html; th.scrollTop = th.scrollHeight;
  const pend = list.filter(m => m.st === 'pending').length;
  $('#pendBar').hidden = !pend || isLive;
  if (pend && !isLive) {
    $('#pendTxt').textContent = (pend > 1 ? pend + ' messages attendent' : '1 message attend') + " d'être remis";
    $('#pendBtn').querySelector('span').textContent = c.demo ? 'Remettre le pli à Claude' : 'Préparer le pli';
  }
  const inp = $('#msgInput');
  if (document.activeElement !== inp) { inp.value = S.drafts[c.fp] || ''; grow(); }
}
function renderAll(){ renderMe(); renderList(); renderChat(); renderFoot(); }

function openContact(fp){
  current = fp; const c = S.contacts[fp]; if (c) c.unread = 0;
  $('#app').dataset.view = 'chat'; save(); renderList();
  const inp = $('#msgInput'); inp.value = S.drafts[fp] || ''; renderChat();
  if (!coarse) inp.focus();
}

/* ---------- feuilles ---------- */
let sheetCleanup = null, sheetTag = null;
function openSheet(title, html, mount, tag){
  if (typeof sheetCleanup === 'function') { const f = sheetCleanup; sheetCleanup = null; f(); }
  $('#sheetTitle').textContent = title; $('#sheetBody').innerHTML = html; $('#scrim').hidden = false; sheetTag = tag || null;
  $('#sheetBody').scrollTop = 0; $('.sheet').scrollTop = 0;
  sheetCleanup = mount ? mount($('#sheetBody')) : null;
  const f = $('#sheetBody').querySelector('[autofocus]'); if (f && !coarse) f.focus();
}
function closeSheet(){ $('#scrim').hidden = true; sheetTag = null; if (typeof sheetCleanup === 'function') { const f = sheetCleanup; sheetCleanup = null; f(); } }
$('#sheetClose').onclick = closeSheet;
$('#scrim').addEventListener('click', e => { if (e.target.id === 'scrim') closeSheet(); });
document.addEventListener('keydown', e => { if (e.key === 'Escape' && !$('#scrim').hidden) closeSheet(); });

async function copyText(text, ta){
  try { await navigator.clipboard.writeText(text); return true; } catch(e) {}
  try { if (ta) { ta.focus(); ta.select(); } if (document.execCommand('copy')) return true; } catch(e) {}
  if (ta) { ta.focus(); ta.select(); }
  toast('Copie automatique bloquée ici : le code est sélectionné, copiez-le vous-même.', 4500);
  return false;
}
async function saveFile(name, text){
  if (dlCap) {
    try { await dlCap.save({filename:name, data:text}); return true; }
    catch(e) { if (!e || e.code !== 'declined') toast("L'enregistrement n'est pas possible ici. Copiez le code."); return false; }
  }
  const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([text], {type:'text/plain'})); a.download = name;
  document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1000);
  return true;
}
function codeBlock(code){
  return `<textarea class="code" readonly rows="4" aria-label="Code">${esc(code)}</textarea>
  <div class="actions"><button class="btn" type="button" data-act="copy">Copier le code</button>${canShare ? '<button class="btn" type="button" data-act="share">Partager…</button>' : ''}${canSave() ? '<button class="btn" type="button" data-act="save">Enregistrer en fichier</button>' : ''}</div>`;
}
function wireCode(root, code, fname, onDone){
  const ta = root.querySelector('textarea.code[readonly]');
  ta.addEventListener('focus', () => ta.select());
  root.querySelector('[data-act=copy]').onclick = async () => { if (await copyText(code, ta)) { toast('Code copié'); onDone && onDone('copy'); } };
  const sh = root.querySelector('[data-act=share]');
  if (sh) sh.onclick = async () => {
    try {
      const file = new File([code], fname, {type:'text/plain'});
      if (navigator.canShare && navigator.canShare({files:[file]})) await navigator.share({files:[file], title:fname});
      else await navigator.share({title:'Pli', text:code});
      onDone && onDone('share');
    } catch(e) { if (e.name !== 'AbortError') toast("Le partage n'est pas disponible ici. Copiez le code ou enregistrez le fichier."); }
  };
  const sv = root.querySelector('[data-act=save]');
  if (sv) sv.onclick = async () => { if (await saveFile(fname, code)) { toast('Fichier enregistré : ' + fname); onDone && onDone('save'); } };
}
const slug = s => (s || 'contact').normalize('NFD').replace(/[̀-ͯ]/g,'').replace(/[^a-zA-Z0-9]+/g,'-').replace(/^-|-$/g,'').toLowerCase() || 'contact';
function armButton(btn, label, action){
  let armed = false, t; const old = btn.textContent;
  btn.addEventListener('click', () => {
    if (!armed) { armed = true; btn.textContent = label; btn.classList.add('armed');
      t = setTimeout(() => { armed = false; btn.textContent = old; btn.classList.remove('armed'); }, 4000); return; }
    clearTimeout(t); action();
  });
}

/* Ma carte */
function sheetMyCard(){
  const code = cardCode(S.me);
  openSheet('Ma carte de contact', `
    ${qrOrNote(code, 'M', 'Cette carte')}
    <p class="qr-cap">Faites scanner ce QR avec Pli, depuis « Ajouter » sur l'autre appareil.</p>
    <dl class="kv"><dt>Votre empreinte</dt><dd>${fmtFp(S.me.fp)}</dd></dl>
    <p class="note">Comparez cette empreinte avec ce que votre contact voit : si elle correspond, personne n'a remplacé votre carte en chemin.</p>
    <details><summary>Envoyer la carte autrement</summary><div class="more">
      <p class="note">La carte ne contient que votre nom et votre clé publique : elle peut circuler sans risque, par SMS, Bluetooth ou e-mail.</p>
      ${codeBlock(code)}</div></details>
    <hr class="sep">
    <div class="field"><label for="renameMe">Nom affiché</label><input class="input" id="renameMe" maxlength="60" value="${esc(S.me.name)}"></div>
    <div class="actions"><button class="btn" type="button" id="saveName">Enregistrer le nom</button></div>
  `, root => {
    wireCode(root, code, `carte-${slug(S.me.name)}.txt`);
    root.querySelector('#saveName').onclick = () => { const v = root.querySelector('#renameMe').value.trim(); if (!v) return; S.me.name = v; save(); renderMe(); closeSheet(); toast("Nom mis à jour. Renvoyez votre carte pour qu'il apparaisse chez vos contacts."); };
  });
}

/* Ajouter / Recevoir */
function sheetReceive(mode){
  const isAdd = mode === 'add';
  openSheet(isAdd ? 'Ajouter un contact' : 'Recevoir', `
    <p>${isAdd ? 'Scannez le QR de la carte de votre contact (dans Pli, « Ma carte » sur son appareil).' : 'Scannez un pli, une carte ou un code de discussion en direct affiché sur un autre appareil.'}</p>
    ${scannerHTML(isAdd ? 'Scanner sa carte' : 'Scanner un QR')}
    <hr class="sep">
    <div class="field"><label for="pasteIn">Ou collez le code reçu</label>
    <textarea class="code" id="pasteIn" rows="3" placeholder="${isAdd ? 'CARTE1.…' : 'PLI1.…  CARTE1.…  LIEN1.…'}"></textarea></div>
    <div class="drop">ou <label for="fileIn">choisissez un fichier</label> reçu par Bluetooth, AirDrop ou clé USB<input type="file" id="fileIn" accept=".pli,.txt,text/plain" multiple hidden></div>
    <button class="btn primary" type="button" id="openBtn">${isAdd ? 'Ajouter le contact' : 'Ouvrir'}</button>
  `, root => {
    root.querySelector('#openBtn').onclick = () => handleIncoming(root.querySelector('#pasteIn').value, true);
    root.querySelector('#fileIn').onchange = async e => { const txt = (await Promise.all([...e.target.files].map(f => f.text()))).join('\n'); handleIncoming(txt, true); };
    return wireScanner(root, txt => handleIncoming(txt, true));
  });
}

/* Préparer un pli */
async function preparePli(){
  const c = S.contacts[current]; if (!c) return;
  const pend = (S.msgs[c.fp] || []).filter(m => m.st === 'pending');
  if (!pend.length) return;
  const code = await seal(S.me, c.pub, c.fp, {n:S.me.name, m:pend.map(m => ({id:m.id, t:m.t, b:m.b}))});
  const markSent = () => { pend.forEach(m => m.st = 'sent'); save(); renderList(); renderChat(); };
  if (c.demo) return demoDeliver(code, markSent);
  const stamp = new Date().toISOString().slice(0,16).replace(/[-:T]/g,'');
  openSheet('Pli pour ' + c.name, `
    <p>${plural(pend.length, 'message scellé', 'messages scellés')} · ${fmtBytes(code.length)}. Seul l'appareil de ${esc(c.name)} peut l'ouvrir.</p>
    ${qrOrNote(code, 'L', 'Ce pli')}
    ${code.length <= QR_MAX && HAS_QR ? `<p class="qr-cap">${esc(c.name)} le scanne avec « Recevoir » dans Pli.</p>` : ''}
    <details ${code.length > QR_MAX || !HAS_QR ? 'open' : ''}><summary>Envoyer le pli autrement</summary><div class="more">
      <p class="note">Bluetooth, AirDrop, Partage à proximité, clé USB, SMS ou e-mail : le canal n'a pas d'importance.</p>
      ${codeBlock(code)}</div></details>
    <button class="btn primary" type="button" id="manualSent">Pli remis à ${esc(c.name)}</button>
  `, root => {
    wireCode(root, code, `pli-${slug(c.name)}-${stamp}.txt`, () => markSent());
    root.querySelector('#manualSent').onclick = () => { markSent(); closeSheet(); toast('Messages marqués comme remis.'); };
  });
}

/* Détails du contact */
function sheetContact(){
  const c = S.contacts[current]; if (!c) return;
  openSheet(c.name, `
    <dl class="kv"><dt>Son empreinte</dt><dd>${fmtFp(c.fp)}</dd><dt>La vôtre</dt><dd>${fmtFp(S.me.fp)}</dd></dl>
    <p class="note">${c.demo ? 'Ce contact de démonstration est simulé sur votre appareil : ses réponses sont de vrais plis chiffrés, générés localement.' : "Comparez son empreinte avec celle qu'il voit sur son écran, en personne ou au téléphone. Si elles correspondent, la conversation est authentifiée."}</p>
    ${c.verified ? '<p class="note ok">Empreinte vérifiée.</p>' : (c.demo ? '' : '<button class="btn primary" type="button" id="verifyBtn">Les empreintes correspondent</button>')}
    <div class="field"><label for="renameC">Nom du contact</label><input class="input" id="renameC" maxlength="60" value="${esc(c.name)}"></div>
    <div class="actions"><button class="btn" type="button" id="saveC">Renommer</button><button class="btn danger" type="button" id="delC">Supprimer le contact</button></div>
  `, root => {
    const v = root.querySelector('#verifyBtn'); if (v) v.onclick = () => { c.verified = true; save(); renderChat(); closeSheet(); toast('Contact vérifié.'); };
    root.querySelector('#saveC').onclick = () => { const n = root.querySelector('#renameC').value.trim(); if (!n) return; c.name = n; save(); renderList(); renderChat(); closeSheet(); };
    armButton(root.querySelector('#delC'), 'Confirmer la suppression', () => {
      liveDrop(c.fp, true);
      delete S.contacts[c.fp]; delete S.msgs[c.fp]; delete S.drafts[c.fp]; current = null;
      $('#app').dataset.view = 'list'; save(); closeSheet(); renderList(); renderChat(); toast('Contact et conversation supprimés.');
    });
  });
}

/* Réglages et code de verrouillage */
const pinOk = p => /^\d{6,12}$/.test(p);
const pinField = (id, label, extra = '') => `<div class="field"><label for="${id}">${label}</label><input class="input" id="${id}" type="password" inputmode="numeric" pattern="[0-9]*" autocomplete="off" maxlength="12" ${extra}></div>`;
async function verifyPin(pin){
  if (!lockMeta) return false;
  const raw = store.read(); if (!raw || !raw.lock) return false;
  try {
    const k = await pinKey(pin, unb64u(raw.lock.salt), raw.lock.iter);
    await crypto.subtle.decrypt({name:'AES-GCM', iv:unb64u(raw.iv)}, k, unb64u(raw.c));
    return true;
  } catch(e) { return false; }
}
async function setPin(pin){
  const salt = rand(16);
  lockKey = await pinKey(pin, salt, PIN_ITER);
  lockMeta = {salt:b64u(salt), iter:PIN_ITER, len:pin.length};
  await flushSave(); renderMe(); renderFoot();
}
function sheetSettings(){
  const on = !!lockMeta, a = S.settings.autoLock;
  const opts = [[1,'1 minute'],[5,'5 minutes'],[15,'15 minutes'],[60,'1 heure'],[0,'Jamais (verrouillage manuel)']];
  openSheet('Réglages', `
    <section class="group"><h3>Code de verrouillage</h3>
    ${!store.ok ? '<p class="note">Indisponible : ce navigateur ne garde rien sur l\'appareil, il n\'y a donc rien à verrouiller.</p>' : on ? `
      <p class="note ok">Activé. Votre identité, vos contacts et vos messages sont chiffrés avec votre code sur cet appareil.</p>
      <div class="field"><label for="autoLock">Verrouiller après une inactivité de</label>
      <select class="input" id="autoLock">${opts.map(([v,l]) => `<option value="${v}" ${v === a ? 'selected' : ''}>${l}</option>`).join('')}</select></div>
      <button class="btn primary" type="button" id="lockNowBtn"><svg><use href="#i-lock"/></svg>Verrouiller maintenant</button>
      <details><summary>Changer ou désactiver le code</summary><form class="more" id="pinChange">
        ${pinField('pinCur', 'Code actuel')}
        ${pinField('pinNew', 'Nouveau code (6 à 12 chiffres)')}
        ${pinField('pinNew2', 'Confirmez le nouveau code')}
        <p class="note" id="pinMsg2" aria-live="polite"></p>
        <div class="actions"><button class="btn primary" type="submit" id="chgBtn">Changer le code</button><button class="btn danger" type="button" id="offBtn">Désactiver le code</button></div>
      </form></details>` : `
      <p class="note">Protégez l'accès à Pli avec un code de 6 à 12 chiffres. Tout ce que Pli garde sur cet appareil sera chiffré avec ce code.</p>
      <form class="more" id="pinSet">
        ${pinField('pinNew', 'Nouveau code', 'autofocus')}
        ${pinField('pinNew2', 'Confirmez le code')}
        <p class="note" id="pinMsg" aria-live="polite"></p>
        <button class="btn primary" type="submit" id="setPinBtn"><svg><use href="#i-lock"/></svg>Activer le verrouillage</button>
      </form>
      <p class="fine">Le code ne peut pas être récupéré. Si vous l'oubliez, il faudra tout effacer et recommencer.</p>`}
    </section>
    <hr class="sep">
    <section class="group"><h3>Sauvegarde du compte</h3>
      <p class="note">${S.settings.lastBackup ? 'Dernière sauvegarde : ' + dFmt.format(new Date(S.settings.lastBackup)) + ' à ' + tFmt.format(new Date(S.settings.lastBackup)) + '.' : "Aucune sauvegarde pour l'instant. Sans elle, changer de téléphone ou effacer le navigateur fait perdre votre compte."}</p>
      <div class="actions"><button class="btn primary" type="button" id="bakBtn">Sauvegarder mon compte</button><button class="btn" type="button" id="restBtn">Restaurer une sauvegarde</button></div>
    </section>
    <hr class="sep">
    <section class="group"><h3>Cet appareil</h3>
      <p class="note">Efface votre identité, vos contacts et tous les messages enregistrés dans ce navigateur.</p>
      <button class="btn danger" type="button" id="wipeBtn">Effacer cet appareil</button>
    </section>
  `, root => {
    const q = s => root.querySelector(s);
    armButton(q('#wipeBtn'), 'Confirmer : tout effacer', wipeAll);
    q('#bakBtn').onclick = sheetBackup;
    q('#restBtn').onclick = () => sheetRestore();
    if (!store.ok) return;
    if (!on) {
      q('#pinSet').addEventListener('submit', async e => {
        e.preventDefault(); const p1 = q('#pinNew').value, p2 = q('#pinNew2').value, msg = q('#pinMsg');
        if (!pinOk(p1)) { msg.className = 'note err'; msg.textContent = 'Le code doit compter 6 à 12 chiffres.'; return; }
        if (p1 !== p2) { msg.className = 'note err'; msg.textContent = 'Les deux codes sont différents.'; return; }
        const b = q('#setPinBtn'); b.disabled = true; msg.className = 'note'; msg.textContent = 'Chiffrement des données…';
        await setPin(p1); closeSheet(); toast('Verrouillage activé.');
      });
      return;
    }
    q('#autoLock').onchange = e => { S.settings.autoLock = Number(e.target.value); save(); toast('Délai enregistré.'); };
    q('#lockNowBtn').onclick = () => lockNow();
    const msg = q('#pinMsg2');
    const busy = v => { q('#chgBtn').disabled = v; q('#offBtn').disabled = v; };
    q('#pinChange').addEventListener('submit', async e => {
      e.preventDefault(); const cur = q('#pinCur').value, p1 = q('#pinNew').value, p2 = q('#pinNew2').value;
      if (!pinOk(p1)) { msg.className = 'note err'; msg.textContent = 'Le nouveau code doit compter 6 à 12 chiffres.'; return; }
      if (p1 !== p2) { msg.className = 'note err'; msg.textContent = 'Les deux nouveaux codes sont différents.'; return; }
      busy(true); msg.className = 'note'; msg.textContent = 'Vérification…';
      if (!(await verifyPin(cur))) { busy(false); msg.className = 'note err'; msg.textContent = 'Le code actuel est incorrect.'; return; }
      await setPin(p1); closeSheet(); toast('Code modifié.');
    });
    q('#offBtn').onclick = async () => {
      busy(true); msg.className = 'note'; msg.textContent = 'Vérification…';
      if (!(await verifyPin(q('#pinCur').value))) { busy(false); msg.className = 'note err'; msg.textContent = 'Saisissez votre code actuel pour désactiver le verrouillage.'; return; }
      lockMeta = null; lockKey = null; await flushSave(); renderMe(); renderFoot(); closeSheet(); toast('Verrouillage désactivé. Les données ne sont plus protégées par un code.');
    };
  });
}
/* ---------- sauvegarde et restauration du compte ----------
   SAUV1 = PBKDF2-SHA256 (600 000 itérations) sur la phrase secrète -> AES-GCM 256,
   appliqué au compte compressé. La phrase secrète n'est jamais enregistrée. */
const BAK_ITER = 600000, BAK_AD = enc.encode('pli-sauv/1');
const passOk = p => p.length >= 8;
async function makeBackup(pass, withMsgs){
  const msgs = {};
  for (const fp of Object.keys(S.contacts)) msgs[fp] = withMsgs ? (S.msgs[fp] || []) : [];
  const data = {v:1, at:Date.now(), me:S.me, demo:S.demo, contacts:S.contacts, msgs, settings:S.settings};
  const plain = await zpack(data);
  const salt = rand(16), iv = rand(12);
  const key = await pinKey(pass.normalize('NFC'), salt, BAK_ITER);
  const c = await crypto.subtle.encrypt({name:'AES-GCM', iv, additionalData:BAK_AD}, key, enc.encode(plain));
  return 'SAUV1.' + packJSON({v:1, s:b64u(salt), n:BAK_ITER, i:b64u(iv), c:b64u(c)});
}
async function openBackup(code, pass){
  let o; try { o = unpackJSON(code.slice(6)); } catch(e) { throw new Error('damaged'); }
  if (!o || !o.c || !o.s || !o.i) throw new Error('damaged');
  const iter = Math.min(Math.max(Number(o.n) || BAK_ITER, 100000), 5000000);
  const key = await pinKey(pass.normalize('NFC'), unb64u(o.s), iter);
  let pt; try { pt = await crypto.subtle.decrypt({name:'AES-GCM', iv:unb64u(o.i), additionalData:BAK_AD}, key, unb64u(o.c)); }
  catch(e) { throw new Error('pass'); }
  let data; try { data = await zunpack(dec.decode(pt)); } catch(e) { throw new Error('damaged'); }
  if (!data || !data.me || !data.me.priv || !data.me.pub || !data.me.pub.x) throw new Error('damaged');
  return data;
}
async function applyRestore(data){
  for (const fp of [...live.keys()]) liveDrop(fp, true);
  abortRtc(rtcPending); keyCache.clear(); liveQueue.length = 0;
  const st = migrate(Object.assign(emptyState(), {
    me:data.me, demo:data.demo || null, contacts:data.contacts || {}, msgs:data.msgs || {},
    settings:Object.assign({autoLock:5}, data.settings || {}),
  }));
  st.me.fp = await fingerprint(st.me.pub);
  await crypto.subtle.importKey('jwk', st.me.priv, EC, false, ['deriveBits']);   // clé privée valide ?
  for (const fp of Object.keys(st.contacts)) if (!Array.isArray(st.msgs[fp])) st.msgs[fp] = [];
  S = st; current = null;
  await flushSave();
  closeSheet(); $('#onboard').hidden = true; $('#lock').hidden = true; boot();
}
function sheetBackup(){
  const nMsgs = Object.values(S.msgs).reduce((a, l) => a + l.length, 0);
  openSheet('Sauvegarder mon compte', `
    <p>La sauvegarde contient votre identité (vos clés), vos contacts et, si vous le voulez, vos messages. Elle est chiffrée avec une phrase secrète : sans elle, personne ne peut l'ouvrir.</p>
    <form class="more" id="bakForm">
      <div class="field"><label for="bakP1">Phrase secrète (8 caractères minimum)</label><input class="input" id="bakP1" type="password" autocomplete="new-password" autofocus></div>
      <div class="field"><label for="bakP2">Confirmez la phrase secrète</label><input class="input" id="bakP2" type="password" autocomplete="new-password"></div>
      <label class="check"><input type="checkbox" id="bakMsgs" ${nMsgs ? 'checked' : ''}><span>Inclure les messages (${nMsgs})</span></label>
      <p class="note" id="bakMsg" aria-live="polite"></p>
      <button class="btn primary" type="submit" id="bakMake">Créer la sauvegarde</button>
    </form>
    <p class="fine">Choisissez une phrase facile à retenir mais longue, par exemple quatre mots sans rapport. Elle n'est enregistrée nulle part : notez-la à part.</p>
    <div class="group" id="bakOut" hidden></div>
  `, root => {
    const q = s => root.querySelector(s), msg = q('#bakMsg');
    q('#bakForm').addEventListener('submit', async e => {
      e.preventDefault(); const p1 = q('#bakP1').value, p2 = q('#bakP2').value;
      if (!passOk(p1)) { msg.className = 'note err'; msg.textContent = 'La phrase secrète doit compter au moins 8 caractères.'; return; }
      if (p1 !== p2) { msg.className = 'note err'; msg.textContent = 'Les deux phrases sont différentes.'; return; }
      q('#bakMake').disabled = true; msg.className = 'note'; msg.textContent = 'Chiffrement de la sauvegarde…';
      let code;
      try { code = await makeBackup(p1, q('#bakMsgs').checked); }
      catch(err) { q('#bakMake').disabled = false; msg.className = 'note err'; msg.textContent = "La sauvegarde n'a pas pu être créée. Réessayez."; return; }
      S.settings.lastBackup = Date.now(); save(); renderFoot();
      const day = new Date().toISOString().slice(0,10);
      q('#bakForm').hidden = true; root.querySelector('.fine').hidden = true;
      const out = q('#bakOut'); out.hidden = false;
      out.innerHTML = `
        <p class="note ok">Sauvegarde prête · ${fmtBytes(code.length)}.</p>
        <p>Enregistrez-la <b>hors de cet appareil</b> : sur un ordinateur, une clé USB, ou envoyez-la-vous par e-mail. Pour la restaurer : « J'ai déjà un compte » au premier écran de Pli.</p>
        ${code.length <= QR_MAX && HAS_QR ? qrSvg(code, 'L') + '<p class="qr-cap">Vous pouvez aussi photographier ce QR.</p>' : ''}
        ${codeBlock(code)}`;
      wireCode(out, code, `pli-sauvegarde-${slug(S.me.name)}-${day}.txt`, kind => { if (kind === 'save') toast('Sauvegarde enregistrée.'); });
    });
  });
}
const BAK_RE = /SAUV1\.[A-Za-z0-9_-]+/;
function sheetRestore(prefill){
  const hasAccount = !!S.me;
  openSheet('Restaurer un compte', `
    ${hasAccount ? "<p class=\"note err\">La restauration remplace l'identité, les contacts et les messages actuels de cet appareil.</p>" : ''}
    <p>Choisissez le fichier de sauvegarde, scannez son QR ou collez son code (il commence par <span class="fp">SAUV1.</span>).</p>
    <div class="drop"><label for="bakFile">Choisir le fichier de sauvegarde</label><input type="file" id="bakFile" accept=".txt,.pli,text/plain" hidden></div>
    ${scannerHTML('Scanner le QR de sauvegarde')}
    <div class="field"><label for="bakIn">Code de sauvegarde</label><textarea class="code" id="bakIn" rows="3" placeholder="SAUV1.…">${esc(prefill || '')}</textarea></div>
    <div class="field"><label for="bakPass">Phrase secrète</label><input class="input" id="bakPass" type="password" autocomplete="current-password"></div>
    <p class="note" id="bakMsg" aria-live="polite"></p>
    <button class="btn primary" type="button" id="bakGo">Restaurer mon compte</button>
  `, root => {
    const q = s => root.querySelector(s), msg = q('#bakMsg'), go = q('#bakGo');
    const say = (t, cls) => { msg.className = 'note' + (cls ? ' ' + cls : ''); msg.textContent = t; };
    const setCode = txt => {
      const m = (txt || '').replace(/\s+/g, '').match(BAK_RE);
      if (!m) { say("Ce n'est pas une sauvegarde Pli : elle commence par SAUV1.", 'err'); return; }
      q('#bakIn').value = m[0]; say('Sauvegarde chargée. Saisissez maintenant la phrase secrète.', 'ok');
      if (!coarse) q('#bakPass').focus();
    };
    q('#bakFile').onchange = async e => { const f = e.target.files && e.target.files[0]; e.target.value = ''; if (f) setCode(await f.text()); };
    q('#bakPass').addEventListener('keydown', e => { if (e.key === 'Enter') go.click(); });
    let armed = false;
    go.onclick = async () => {
      const m = q('#bakIn').value.replace(/\s+/g, '').match(BAK_RE), pass = q('#bakPass').value;
      if (!m) { say("Ajoutez d'abord la sauvegarde : fichier, QR ou code.", 'err'); return; }
      if (!pass) { say('Saisissez la phrase secrète choisie lors de la sauvegarde.', 'err'); return; }
      if (hasAccount && !armed) { armed = true; go.textContent = 'Confirmer : remplacer le compte actuel'; go.classList.remove('primary'); go.classList.add('danger', 'armed'); return; }
      go.disabled = true; say('Déchiffrement…');
      try {
        const data = await openBackup(m[0], pass);
        await applyRestore(data);
        const n = Object.values(S.contacts).filter(c => !c.demo).length;
        toast(`Compte de ${S.me.name} restauré · ${plural(n, 'contact', 'contacts')}.`, 4000);
      } catch(e) {
        go.disabled = false;
        say(e.message === 'pass' ? 'Phrase secrète incorrecte.' : 'Cette sauvegarde est abîmée ou incomplète.', 'err');
      }
    };
    return wireScanner(root, txt => setCode(txt));
  });
}
function wipeAll(){
  for (const fp of [...live.keys()]) liveDrop(fp, true);
  abortRtc(rtcPending);
  store.wipe(); S = emptyState(); current = null; keyCache.clear(); lockMeta = null; lockKey = null; liveQueue.length = 0;
  closeSheet(); $('#lock').hidden = true; $('#app').hidden = true; showOnboard(); toast('Identité, contacts et messages effacés.');
}

/* ---------- réception ---------- */
const ERR = {
  'not-for-me': "Un pli est adressé à quelqu'un d'autre : il ne peut pas être ouvert sur cet appareil.",
  'damaged': "Un code est abîmé ou incomplet. Demandez à l'expéditeur de le renvoyer en entier.",
  'self': "C'est votre propre carte de contact.",
};
function ensureContact(fp, name, pub){
  let c = S.contacts[fp];
  if (!c) { c = S.contacts[fp] = {fp, name:String(name || 'Contact').slice(0,60), pub:{x:pub.x, y:pub.y}, verified:false, added:Date.now(), unread:0}; S.msgs[fp] = []; return [c, true]; }
  return [c, false];
}
function ingest(fromFp, fromPub, payload){
  const [c, isNew] = ensureContact(fromFp, payload.n || 'Inconnu', fromPub);
  const list = S.msgs[fromFp]; const ids = new Set(list.map(m => m.id));
  let added = 0, dup = 0;
  for (const m of (payload.m || [])) {
    if (!m || ids.has(String(m.id))) { dup++; continue; }
    list.push({id:String(m.id), dir:'in', t:Number(m.t) || Date.now(), b:String(m.b).slice(0,20000), st:'recv'});
    ids.add(String(m.id)); added++;
    if (current !== fromFp || document.hidden) c.unread = (c.unread || 0) + 1;
  }
  list.sort((a,b) => a.t - b.t);
  return {added, dup, isNew};
}
const TOKEN_RE = /(?:PLI1|CARTE1|LIEN1|REP1|SAUV1)\.[A-Za-z0-9_-]+/g;
async function receiveText(tokens){
  const r = {cards:0, known:0, msgs:0, dup:0, newContacts:0, errors:[], lastFp:null};
  for (const t of tokens) {
    try {
      if (t.startsWith('CARTE1.')) {
        let o; try { o = unpackJSON(t.slice(7)); } catch(e) { throw new Error('damaged'); }
        if (!o || !o.k || !o.k.x || !o.k.y) throw new Error('damaged');
        const fp = await fingerprint(o.k);
        if (fp === S.me.fp) throw new Error('self');
        const [, isNew] = ensureContact(fp, o.n, o.k);
        isNew ? r.cards++ : r.known++; r.lastFp = fp;
      } else {
        const {fromFp, fromPub, payload} = await openPli(t, S.me);
        const g = ingest(fromFp, fromPub, payload);
        r.msgs += g.added; r.dup += g.dup; if (g.isNew) r.newContacts++; r.lastFp = fromFp;
      }
    } catch(e) { const k = ERR[e.message] ? e.message : 'damaged'; if (!r.errors.includes(ERR[k])) r.errors.push(ERR[k]); }
  }
  save(); return r;
}
async function handleIncoming(text, fromSheet){
  if (!S.me) return;
  const tokens = [...new Set((text || '').replace(/\s+/g, '').match(TOKEN_RE) || [])];
  if (!tokens.length) { toast('Aucun code Pli trouvé. Un pli commence par PLI1., une carte par CARTE1.', 4000); return; }
  const lien = tokens.find(t => t.startsWith('LIEN1.')), rep = tokens.find(t => t.startsWith('REP1.'));
  const sauv = tokens.find(t => t.startsWith('SAUV1.'));
  if (sauv) return sheetRestore(sauv);
  if (lien) return startResponder(lien);
  if (rep) return applyAnswer(rep);
  const r = await receiveText(tokens);
  const parts = [];
  if (r.msgs) parts.push(plural(r.msgs, 'nouveau message', 'nouveaux messages'));
  if (r.cards) parts.push(plural(r.cards, 'contact ajouté', 'contacts ajoutés'));
  if (r.newContacts) parts.push(r.newContacts > 1 ? r.newContacts + ' expéditeurs ajoutés' : 'expéditeur ajouté à vos contacts');
  if (!r.msgs && r.dup) parts.push('déjà reçu');
  if (r.known && !r.cards) parts.push('contact déjà connu');
  if (r.errors.length) parts.push(r.errors.join(' '));
  toast(parts.join(' · '), r.errors.length ? 5500 : 3200);
  if (fromSheet && !r.errors.length) closeSheet();
  renderList();
  if (r.lastFp && (r.msgs || r.cards || r.known)) openContact(r.lastFp); else renderChat();
}

/* ---------- discussion en direct : WebRTC sur le réseau local, signalé par QR ---------- */
const live = new Map();          // fp -> {pc, dc, authed}
const liveQueue = [];            // trames chiffrées reçues pendant le verrouillage
let rtcPending = null;           // connexion en cours de préparation
const isLiveOpen = fp => { const L = live.get(fp); return !!(L && L.dc && L.dc.readyState === 'open'); };
const NO_NET = "Aucun réseau local trouvé. Connectez les deux appareils au même Wi-Fi (ou au partage de connexion de l'un d'eux), même sans Internet.";
function newPc(){ return new RTCPeerConnection({iceServers:[]}); }
function waitIce(pc){
  if (pc.iceGatheringState === 'complete') return Promise.resolve();
  return new Promise(res => {
    const t = setTimeout(res, 5000);
    pc.addEventListener('icegatheringstatechange', () => { if (pc.iceGatheringState === 'complete') { clearTimeout(t); res(); } });
  });
}
const hasCand = sdp => /a=candidate/.test(sdp);
function abortRtc(ctx){ if (!ctx || ctx.linked) return; try { ctx.pc.close(); } catch(e) {} if (rtcPending === ctx) rtcPending = null; }
function setStatus(root, cls, text, spin){
  const el = root && root.querySelector('.status'); if (!el) return;
  el.className = 'status ' + (cls || ''); el.innerHTML = (spin ? '<span class="spin"></span>' : '') + esc(text);
}
function wireRtc(ctx){
  const onOpen = dc => { dc.onopen = () => linkLive(ctx, dc); if (dc.readyState === 'open') linkLive(ctx, dc); };
  if (ctx.dc) onOpen(ctx.dc);
  ctx.pc.ondatachannel = e => { ctx.dc = e.channel; onOpen(e.channel); };
  ctx.pc.onconnectionstatechange = () => {
    if (ctx.linked) return;
    const st = ctx.pc.connectionState;
    if (st === 'connecting') setStatus(ctx.root, '', 'Connexion en cours…', true);
    if (st === 'failed') setStatus(ctx.root, 'err', "La connexion a échoué. Vérifiez que les deux appareils sont sur le même Wi-Fi et que le réseau n'isole pas les appareils (Wi-Fi invité), puis recommencez.");
  };
}
function liveIntro(){
  return '<p class="note">Les deux appareils doivent être sur le même Wi-Fi, ou l\'un connecté au partage de connexion de l\'autre. Internet n\'est pas nécessaire.</p>';
}
function sheetLiveUnavailable(){
  openSheet('Discussion en direct', `
    <p>La discussion en direct relie deux appareils sur le même Wi-Fi, sans Internet. Elle a besoin d'une connexion directe entre navigateurs, que cette page en ligne n'autorise pas.</p>
    <p class="note">Ouvrez le fichier <b>Pli-hors-ligne.html</b> dans Chrome, Edge, Firefox ou Safari sur les deux appareils : la fonction « Direct » y est disponible. Les plis et les QR codes fonctionnent partout.</p>
    <button class="btn primary" type="button" id="okLive">Compris</button>`, root => { root.querySelector('#okLive').onclick = closeSheet; });
}
async function startInitiator(fp){
  if (!RTC_OK) return sheetLiveUnavailable();
  const c = S.contacts[fp]; if (!c) return;
  abortRtc(rtcPending);
  const pc = newPc(); const dc = pc.createDataChannel('pli', {ordered:true});
  const ctx = rtcPending = {pc, dc, fp, role:'init', linked:false, root:null};
  wireRtc(ctx);
  openSheet('Direct avec ' + c.name, `${liveIntro()}<div class="status"><span class="spin"></span>Préparation de la connexion…</div>`,
    root => { ctx.root = root; return () => abortRtc(ctx); }, 'live');
  try {
    await pc.setLocalDescription(await pc.createOffer());
    await waitIce(pc);
    if (rtcPending !== ctx) return;
    if (!hasCand(pc.localDescription.sdp)) throw new Error('nonet');
    const code = 'LIEN1.' + await zpack({v:1, n:S.me.name, k:S.me.pub, t:fp, sdp:pc.localDescription.sdp});
    const root = ctx.root;
    root.innerHTML = `
      <ol class="flow">
        <li><h3>Faites scanner ce QR à ${esc(c.name)}</h3>
          <p class="note">Sur son appareil : Pli, puis « Recevoir », puis « Scanner un QR ».</p>
          ${qrOrNote(code, 'L', 'Ce code')}
          <details><summary>Pas de caméra ? Envoyer le code</summary><div class="more">${codeBlock(code)}</div></details></li>
        <li><h3>Scannez la réponse affichée par ${esc(c.name)}</h3>
          ${scannerHTML('Scanner sa réponse')}
          <details><summary>Coller la réponse</summary><div class="more">
            <textarea class="code" id="repIn" rows="3" placeholder="REP1.…" aria-label="Code de réponse"></textarea>
            <button class="btn" type="button" id="repBtn">Valider la réponse</button></div></details></li>
      </ol>
      <div class="status">En attente de la réponse de ${esc(c.name)}…</div>`;
    wireCode(root, code, `direct-${slug(c.name)}.txt`);
    const stopScan = wireScanner(root, txt => { const m = (txt.replace(/\s+/g,'').match(TOKEN_RE) || []).find(t => t.startsWith('REP1.')); if (m) applyAnswer(m); else setStatus(root, 'err', "Ce QR n'est pas une réponse de connexion. Scannez le QR affiché par votre contact après qu'il a scanné le vôtre."); });
    root.querySelector('#repBtn').onclick = () => { const m = (root.querySelector('#repIn').value.replace(/\s+/g,'').match(TOKEN_RE) || []).find(t => t.startsWith('REP1.')); if (m) applyAnswer(m); else setStatus(root, 'err', 'Code de réponse introuvable. Il commence par REP1.'); };
    sheetCleanup = () => { stopScan(); abortRtc(ctx); };
  } catch(e) {
    if (rtcPending === ctx) setStatus(ctx.root, 'err', e.message === 'nonet' ? NO_NET : 'La connexion directe ne peut pas être préparée sur cet appareil.');
    abortRtc(ctx);
  }
}
async function startResponder(token){
  if (!RTC_OK) return sheetLiveUnavailable();
  let o; try { o = await zunpack(token.slice(6)); } catch(e) { toast(ERR.damaged, 4500); return; }
  if (!o || !o.k || !o.sdp) { toast(ERR.damaged, 4500); return; }
  if (o.t && o.t !== S.me.fp) { toast('Ce code de discussion en direct est destiné à un autre appareil.', 4500); return; }
  const fp = await fingerprint(o.k);
  if (fp === S.me.fp) { toast("C'est votre propre code de discussion en direct. Faites-le scanner par votre contact.", 4500); return; }
  const [c, isNew] = ensureContact(fp, o.n, o.k); save(); renderList();
  abortRtc(rtcPending);
  const pc = newPc();
  const ctx = rtcPending = {pc, dc:null, fp, role:'resp', linked:false, root:null};
  wireRtc(ctx);
  openSheet('Direct avec ' + c.name, `${isNew ? `<p class="note ok">${esc(c.name)} a été ajouté à vos contacts.</p>` : ''}<div class="status"><span class="spin"></span>Préparation de la réponse…</div>`,
    root => { ctx.root = root; return () => abortRtc(ctx); }, 'live');
  try {
    await pc.setRemoteDescription({type:'offer', sdp:o.sdp});
    await pc.setLocalDescription(await pc.createAnswer());
    await waitIce(pc);
    if (rtcPending !== ctx) return;
    if (!hasCand(pc.localDescription.sdp)) throw new Error('nonet');
    const code = 'REP1.' + await zpack({v:1, n:S.me.name, k:S.me.pub, t:fp, sdp:pc.localDescription.sdp});
    if (ctx.linked) return;
    ctx.root.innerHTML = `
      ${isNew ? `<p class="note ok">${esc(c.name)} a été ajouté à vos contacts.</p>` : ''}
      <h3>Montrez ce QR à ${esc(c.name)}</h3>
      <p class="note">Il le scanne sur son appareil, dans la fenêtre « Direct » encore ouverte. La connexion s'établit aussitôt.</p>
      ${qrOrNote(code, 'L', 'Ce code')}
      <details><summary>Pas de caméra ? Envoyer le code</summary><div class="more">${codeBlock(code)}</div></details>
      <div class="status"><span class="spin"></span>En attente de ${esc(c.name)}…</div>`;
    wireCode(ctx.root, code, `reponse-${slug(c.name)}.txt`);
  } catch(e) {
    if (rtcPending === ctx) setStatus(ctx.root, 'err', e.message === 'nonet' ? NO_NET : 'Ce code de connexion ne peut pas être utilisé. Demandez à votre contact de recommencer « Direct ».');
    abortRtc(ctx);
  }
}
async function applyAnswer(token){
  const ctx = rtcPending;
  if (!ctx || ctx.role !== 'init') { toast('Aucune connexion directe en préparation. Touchez d\'abord « Direct » dans la conversation.', 4500); return; }
  let o; try { o = await zunpack(token.slice(5)); } catch(e) { setStatus(ctx.root, 'err', ERR.damaged); return; }
  if (!o || !o.k || !o.sdp || o.t !== S.me.fp) { setStatus(ctx.root, 'err', "Cette réponse ne correspond pas à votre invitation."); return; }
  const fp = await fingerprint(o.k);
  if (fp !== ctx.fp) { setStatus(ctx.root, 'err', "Cette réponse vient d'un autre contact que celui que vous avez invité."); return; }
  try { await ctx.pc.setRemoteDescription({type:'answer', sdp:o.sdp}); setStatus(ctx.root, '', 'Connexion en cours…', true); }
  catch(e) { setStatus(ctx.root, 'err', 'Cette réponse a déjà été utilisée ou a expiré. Recommencez « Direct ».'); }
}
function linkLive(ctx, dc){
  if (ctx.linked) return; ctx.linked = true;
  if (rtcPending === ctx) rtcPending = null;
  const fp = ctx.fp, old = live.get(fp);
  if (old && old.pc !== ctx.pc) { try { old.pc.close(); } catch(e) {} }
  const L = {pc:ctx.pc, dc, authed:false, closing:null};
  live.set(fp, L);
  dc.onmessage = e => onLiveFrame(fp, e.data);
  dc.onclose = () => { if (live.get(fp) === L) liveDrop(fp); };
  ctx.pc.onconnectionstatechange = () => {
    const st = ctx.pc.connectionState;
    if (st === 'failed' || st === 'closed') { if (live.get(fp) === L) liveDrop(fp); }
    else if (st === 'disconnected') { clearTimeout(L.closing); L.closing = setTimeout(() => { if (ctx.pc.connectionState !== 'connected' && live.get(fp) === L) liveDrop(fp); }, 8000); }
    else if (st === 'connected') clearTimeout(L.closing);
  };
  if (sheetTag === 'live') { sheetCleanup = null; closeSheet(); }
  if (!S.me) return;
  const c = S.contacts[fp];
  toast('Connecté en direct avec ' + (c ? c.name : 'votre contact'));
  sendLive(fp, {h:1});
  flushLive(fp);
  openContact(fp);
}
function liveDrop(fp, silent){
  const L = live.get(fp); if (!L) return;
  live.delete(fp); clearTimeout(L.closing);
  try { L.dc && L.dc.close(); } catch(e) {} try { L.pc.close(); } catch(e) {}
  if (!S.me) return;
  const c = S.contacts[fp];
  if (!silent && c) toast(`Discussion directe avec ${c.name} terminée. Les messages repassent en mode pli.`, 4500);
  renderList(); renderChat();
}
async function sendLive(fp, payload){
  const L = live.get(fp), c = S.contacts[fp];
  if (!L || !c || L.dc.readyState !== 'open' || !S.me) return false;
  try { L.dc.send(await seal(S.me, c.pub, c.fp, {n:S.me.name, ...payload})); return true; } catch(e) { return false; }
}
function flushLive(fp){
  const pend = (S.msgs[fp] || []).filter(m => m.st === 'pending');
  if (pend.length) sendLive(fp, {m:pend.map(m => ({id:m.id, t:m.t, b:m.b}))});
}
async function onLiveFrame(fp, data){
  if (typeof data !== 'string' || !data.startsWith('PLI1.')) return;
  if (!S.me) { liveQueue.push([fp, data]); renderLockQueue(); return; }
  let r; try { r = await openPli(data, S.me); } catch(e) { return; }
  if (r.fromFp !== fp) return;
  const L = live.get(fp), p = r.payload || {};
  if (p.h && L && !L.authed) { L.authed = true; if (current === fp) renderChat(); }
  if (Array.isArray(p.a)) {
    const ids = new Set(p.a.map(String)); let ch = false;
    for (const m of (S.msgs[fp] || [])) if (m.dir === 'out' && m.st === 'pending' && ids.has(m.id)) { m.st = 'sent'; ch = true; }
    if (ch) { save(); renderList(); if (current === fp) renderChat(); }
  }
  if (Array.isArray(p.m)) {
    if (L && !L.authed) L.authed = true;
    const g = ingest(fp, r.fromPub, p);
    sendLive(fp, {a:p.m.map(m => m.id)});
    if (g.added) {
      save(); renderList();
      if (current === fp) renderChat();
      else { const c = S.contacts[fp]; toast(`${c.name} : ${String(p.m[p.m.length-1].b).slice(0,80)}`); }
    }
  }
}
function renderLockQueue(){
  const el = $('#lockQueue'), n = liveQueue.length;
  el.hidden = !n; if (n) el.textContent = plural(n, 'envoi reçu en direct pendant le verrouillage', 'envois reçus en direct pendant le verrouillage');
}

/* ---------- contact de démonstration ---------- */
async function createDemo(){
  const k = await newKeys(); const fp = await fingerprint(k.pub);
  S.demo = {name:'Claude (démo)', ...k, fp};
  S.contacts[fp] = {fp, name:S.demo.name, pub:k.pub, verified:false, added:Date.now(), demo:true, unread:2};
  const now = Date.now();
  S.msgs[fp] = [
    {id:uid(), dir:'in', t:now - 420000, b:"Bonjour ! Je suis un contact d'exemple, simulé sur votre appareil.", st:'recv'},
    {id:uid(), dir:'in', t:now - 360000, b:"Écrivez-moi quelque chose, puis touchez « Remettre le pli ». Je vous répondrai avec un vrai pli chiffré.", st:'recv'},
  ];
}
async function demoDeliver(code, markSent){
  const d = S.demo; if (!d) return;
  const {payload} = await openPli(code, d);   // Claude ouvre réellement le pli avec sa clé privée
  markSent();
  toast(`Pli de ${fmtBytes(code.length)} remis à Claude. Il répond…`);
  const first = String(payload.m[payload.m.length-1].b).replace(/\s+/g,' ');
  const quote = first.length > 60 ? first.slice(0,57) + '…' : first;
  const reply = `Bien reçu : « ${quote} ». Votre pli faisait ${fmtBytes(code.length)} et n'a pu être ouvert que par ma clé. Pour écrire à une vraie personne, faites-lui scanner le QR de « Ma carte », puis passez en « Direct » si vous êtes sur le même Wi-Fi.`;
  setTimeout(async () => {
    if (!S.me || !S.demo) return;
    const back = await seal(d, S.me.pub, S.me.fp, {n:d.name, m:[{id:uid(), t:Date.now(), b:reply}]});
    await receiveText([back]); renderList(); renderChat();
  }, 1300);
}

/* ---------- composition ---------- */
const inp = $('#msgInput');
function grow(){ inp.style.height = 'auto'; inp.style.height = Math.min(inp.scrollHeight, 150) + 'px'; }
inp.addEventListener('input', () => { grow(); if (current) { S.drafts[current] = inp.value; save(); } });
inp.addEventListener('keydown', e => { if (e.key === 'Enter' && !e.shiftKey && !coarse) { e.preventDefault(); $('#composer').requestSubmit(); } });
$('#composer').addEventListener('submit', e => {
  e.preventDefault(); const b = inp.value.trim(); if (!b || !current) return;
  const m = {id:uid(), dir:'out', t:Date.now(), b, st:'pending'};
  S.msgs[current].push(m);
  S.drafts[current] = ''; inp.value = ''; grow(); save(); renderList(); renderChat(); inp.focus();
  if (isLiveOpen(current)) sendLive(current, {m:[{id:m.id, t:m.t, b:m.b}]});
});
$('#pendBtn').onclick = () => preparePli().catch(() => toast("Le pli n'a pas pu être scellé. Réessayez."));
$('#backBtn').onclick = () => { current = null; $('#app').dataset.view = 'list'; renderList(); renderChat(); };
$('#infoBtn').onclick = sheetContact; $('#cTrust').onclick = sheetContact;
$('#meBtn').onclick = sheetMyCard; $('#addBtn').onclick = () => sheetReceive('add'); $('#recvBtn').onclick = () => sheetReceive('recv');
$('#setBtn').onclick = sheetSettings; $('#lockBtn').onclick = () => lockNow();
(() => {
  const lb = $('#liveBtn'); let armT = null;
  lb.onclick = () => {
    if (!current) return;
    if (!isLiveOpen(current)) return startInitiator(current);
    if (!armT) { lb.querySelector('span').textContent = 'Couper ?'; lb.classList.add('armed');
      armT = setTimeout(() => { armT = null; lb.classList.remove('armed'); renderChat(); }, 3000); return; }
    clearTimeout(armT); armT = null; lb.classList.remove('armed'); sendLive(current, {bye:1}); liveDrop(current);
  };
})();
$('#list').addEventListener('click', e => { const b = e.target.closest('button[data-fp]'); if (b) openContact(b.dataset.fp); });

/* coller un code n'importe où (y compris dans la zone de saisie) l'ouvre directement */
document.addEventListener('paste', e => {
  if (!S.me || !$('#scrim').hidden) return;
  const tgt = e.target; const inField = tgt && (tgt.tagName === 'INPUT' || tgt.tagName === 'TEXTAREA');
  if (inField && tgt !== inp) return;
  const txt = (e.clipboardData || window.clipboardData).getData('text');
  if (/(?:PLI1|CARTE1|LIEN1|REP1|SAUV1)\.[A-Za-z0-9_-]{20,}/.test(txt)) { e.preventDefault(); handleIncoming(txt); }
});
/* glisser-déposer un fichier */
let dragN = 0;
addEventListener('dragenter', e => { if (S.me && e.dataTransfer && [...e.dataTransfer.types].includes('Files')) { dragN++; document.body.classList.add('dropzone-on'); } });
addEventListener('dragleave', () => { dragN = Math.max(0, dragN-1); if (!dragN) document.body.classList.remove('dropzone-on'); });
addEventListener('dragover', e => e.preventDefault());
addEventListener('drop', async e => {
  e.preventDefault(); dragN = 0; document.body.classList.remove('dropzone-on');
  if (!S.me || !e.dataTransfer.files.length) return;
  const txt = (await Promise.all([...e.dataTransfer.files].map(f => f.text()))).join('\n'); handleIncoming(txt);
});

/* ---------- verrouillage ---------- */
let pinBuf = '', pinBusy = false, throttleT = null;
const readFails = () => { try { return JSON.parse(localStorage.getItem(FAILKEY)) || {n:0, until:0}; } catch(e) { return {n:0, until:0}; } };
const writeFails = f => { try { localStorage.setItem(FAILKEY, JSON.stringify(f)); } catch(e) {} };
function drawDots(){
  const len = (lockMeta && lockMeta.len) || Math.max(6, pinBuf.length);
  $('#dots').innerHTML = Array.from({length:len}, (_, i) => `<i class="${i < pinBuf.length ? 'on' : ''}"></i>`).join('');
  $('#okKey').style.visibility = lockMeta && lockMeta.len ? 'hidden' : 'visible';
}
function lockMsg(t, err){ const m = $('#lockMsg'); m.textContent = t; m.className = 'lock-msg' + (err ? ' err' : ''); }
function throttleLeft(){ return Math.max(0, readFails().until - Date.now()); }
function runThrottle(){
  clearInterval(throttleT);
  const tick = () => { const ms = throttleLeft(); if (!ms) { clearInterval(throttleT); lockMsg('Saisissez votre code'); return; } lockMsg(`Trop d'essais. Réessayez dans ${Math.ceil(ms/1000)} s.`, true); };
  tick(); throttleT = setInterval(tick, 500);
}
function showLock(){
  $('#app').hidden = true; $('#onboard').hidden = true; $('#lock').hidden = false;
  pinBuf = ''; drawDots(); renderLockQueue();
  if (throttleLeft()) runThrottle(); else lockMsg('Saisissez votre code');
}
async function lockNow(){
  if (!lockMeta || !lockKey) return;
  await flushSave();
  closeSheet(); abortRtc(rtcPending);
  S = emptyState(); current = null; lockKey = null; keyCache.clear();
  $('#list').innerHTML = ''; $('#thread').innerHTML = ''; inp.value = ''; $('#app').dataset.view = 'list';
  showLock();
}
function pinPress(k){
  if (pinBusy || throttleLeft()) return;
  if (k === 'del') { pinBuf = pinBuf.slice(0, -1); drawDots(); return; }
  if (k === 'ok') { if (pinBuf.length >= 6) submitPin(); return; }
  if (pinBuf.length >= 12) return;
  pinBuf += k; drawDots();
  if (lockMeta && lockMeta.len && pinBuf.length === lockMeta.len) submitPin();
}
async function submitPin(){
  pinBusy = true; lockMsg('Vérification…');
  const raw = store.read(); let ok = false;
  try {
    const k = await pinKey(pinBuf, unb64u(raw.lock.salt), raw.lock.iter);
    const pt = await crypto.subtle.decrypt({name:'AES-GCM', iv:unb64u(raw.iv)}, k, unb64u(raw.c));
    S = migrate(Object.assign(emptyState(), JSON.parse(dec.decode(pt))));
    lockKey = k; lockMeta = raw.lock; ok = true;
  } catch(e) {}
  pinBuf = ''; pinBusy = false;
  if (ok) {
    writeFails({n:0, until:0}); $('#lock').hidden = true; boot();
    const q = liveQueue.splice(0); for (const [fp, data] of q) await onLiveFrame(fp, data);
    for (const fp of live.keys()) { const L = live.get(fp); if (L && !L.authed) sendLive(fp, {h:1}); flushLive(fp); }
    renderList(); renderChat();
    return;
  }
  const f = readFails(); f.n++;
  if (f.n >= 5) f.until = Date.now() + Math.min(15*60000, 30000 * 2 ** (f.n - 5));
  writeFails(f); drawDots();
  const d = $('#dots'); d.classList.remove('shake'); void d.offsetWidth; d.classList.add('shake');
  if (f.until > Date.now()) runThrottle();
  else lockMsg(f.n >= 3 ? `Code incorrect. Encore ${5 - f.n} essai${5 - f.n > 1 ? 's' : ''} avant une attente.` : 'Code incorrect.', true);
}
$('#keypad').addEventListener('click', e => { const b = e.target.closest('[data-k]'); if (b) pinPress(b.dataset.k); });
document.addEventListener('keydown', e => {
  if ($('#lock').hidden) return;
  if (/^\d$/.test(e.key)) pinPress(e.key);
  else if (e.key === 'Backspace') pinPress('del');
  else if (e.key === 'Enter') pinPress('ok');
});
armButton($('#lockWipe'), 'Confirmer : tout effacer', wipeAll);
/* verrouillage automatique */
let lastAct = Date.now(), hiddenAt = 0;
['pointerdown','keydown','touchstart','wheel'].forEach(ev => addEventListener(ev, () => { lastAct = Date.now(); }, {passive:true, capture:true}));
setInterval(() => { const m = S.settings && S.settings.autoLock; if (lockKey && m && Date.now() - lastAct > m*60000) lockNow(); }, 10000);
document.addEventListener('visibilitychange', () => {
  if (document.hidden) { hiddenAt = Date.now(); flushSave(); return; }
  const m = S.settings && S.settings.autoLock;
  if (lockKey && m && hiddenAt && Date.now() - hiddenAt > m*60000) lockNow();
});

/* ---------- démarrage ---------- */
function showOnboard(){ $('#onboard').hidden = false; $('#app').hidden = true; $('#lock').hidden = true; if (!coarse) $('#nameInput').focus(); }
function boot(){
  $('#app').hidden = false; lastAct = Date.now(); renderAll();
  if (!isNarrow()) { const first = $('#list button[data-fp]'); if (first) openContact(first.dataset.fp); }
}
$('#restoreStart').onclick = () => sheetRestore();
$('#onboardForm').addEventListener('submit', async e => {
  e.preventDefault(); const btn = $('#createBtn'); btn.disabled = true; btn.textContent = 'Génération des clés…';
  try {
    const name = $('#nameInput').value.trim() || 'Moi';
    const k = await newKeys(); S = emptyState(); S.me = {name, ...k, fp: await fingerprint(k.pub)};
    await createDemo(); await flushSave();
    $('#onboard').hidden = true; boot();
    if (!isNarrow()) openContact(S.demo.fp);
    if (store.ok) setTimeout(() => toast('Astuce : protégez Pli avec un code dans les réglages.', 4500), 900);
  } catch(err) { toast("La génération des clés a échoué : ce navigateur ne prend pas en charge le chiffrement requis."); }
  btn.disabled = false; btn.textContent = 'Créer mon identité';
});
if (!window.crypto || !crypto.subtle) {
  document.body.innerHTML = '<p style="padding:24px 16px;max-width:520px">Ce navigateur ne propose pas le chiffrement nécessaire à Pli. Ouvrez le fichier dans une version récente de Chrome, Safari, Firefox ou Edge.</p>';
  return;
}
const saved = store.read();
/* migration : l'ancien contact de démonstration devient Claude */
function migrate(st){
  for (const c of Object.values(st.contacts || {})) if (c.demo) c.name = 'Claude (démo)';
  if (st.demo) st.demo.name = 'Claude (démo)';
  return st;
}
if (saved && saved.lock) { lockMeta = saved.lock; showLock(); }
else if (saved && saved.me) { S = migrate(Object.assign(emptyState(), saved)); save(); boot(); }
else { renderFoot(); showOnboard(); }

/* hauteur réelle de l'écran mobile (barre d'adresse, clavier) */
const vv = window.visualViewport;
function fitViewport(){ document.documentElement.style.setProperty('--vh', ((vv ? vv.height : innerHeight) / 100) + 'px'); }
fitViewport(); (vv || window).addEventListener('resize', fitViewport);
inp.addEventListener('focus', () => setTimeout(() => { const th = $('#thread'); th.scrollTop = th.scrollHeight; }, 250));

/* fonctionnement hors ligne une fois l'appli hébergée (https) : cache local */
if (!embedded && 'serviceWorker' in navigator && /^https?:$/.test(location.protocol)) {
  navigator.serviceWorker.register('sw.js').catch(() => {});
}
})();