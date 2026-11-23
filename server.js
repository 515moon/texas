const http = require('http'), fs = require('fs'), path = require('path'), crypto = require('crypto');
const { WebSocketServer } = require('ws');
const PORT = process.env.PORT || 3000, MAX = 6, START_CHIPS = 10000, REBUY = 10000, LEVEL_MS = 5 * 60e3, TURN_MS = 30e3, NEXT_MS = 6000;
const LEVELS = [[50, 100], [75, 150], [100, 200], [150, 300], [200, 400], [300, 600], [400, 800], [500, 1000], [600, 1200], [800, 1600], [1000, 2000], [1500, 3000], [2000, 4000]];
const HAND = ['하이카드', '원페어', '투페어', '트리플', '스트레이트', '플러시', '풀하우스', '포카드', '스트레이트 플러시'];
const rooms = new Map();

const server = http.createServer((q, res) => {
  res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
  res.end(fs.readFileSync(path.join(__dirname, 'public', 'index.html')));
});
const wss = new WebSocketServer({ server });

/* ---------- 카드/족보 ---------- */
const cs = c => '23456789TJQKA'[c.r - 2] + 'shdc'[c.s];
const mkDeck = () => {
  const d = []; for (let s = 0; s < 4; s++)for (let r = 2; r <= 14; r++)d.push({ r, s });
  for (let i = 51; i > 0; i--) { const j = crypto.randomInt(i + 1);[d[i], d[j]] = [d[j], d[i]] } return d
};
function eval5(c) {
  const n = {}; c.forEach(x => n[x.r] = (n[x.r] || 0) + 1);
  let g = Object.keys(n).map(Number).sort((a, b) => n[b] - n[a] || b - a);
  const fl = c.every(x => x.s === c[0].s); let st = false;
  if (g.length === 5) { if (g[0] - g[4] === 4) st = true; else if (g[0] === 14 && g[1] === 5) { st = true; g = [5, 4, 3, 2, 1] } }
  const k = n[g[0]], k2 = n[g[1]] || 0;
  let s = st && fl ? 8 : k === 4 ? 7 : k === 3 && k2 === 2 ? 6 : fl ? 5 : st ? 4 : k === 3 ? 3 : k === 2 && k2 === 2 ? 2 : k === 2 ? 1 : 0;
  for (let i = 0; i < 5; i++)s = s * 15 + (g[i] || 0);
  return s;
}
function best(cards) {
  let b = -1;
  for (let i = 0; i < 7; i++)for (let j = i + 1; j < 7; j++) { const s = eval5(cards.filter((_, k) => k !== i && k !== j)); if (s > b) b = s }
  return b
}

/* ---------- 헬퍼 ---------- */
const note = (r, t) => { r.log.push(t); if (r.log.length > 60) r.log.shift() };
const live = r => r.seats.filter(p => p && p.in && !p.fold);
const canAct = p => p.in && !p.fold && !p.allin;
const nextIdx = (r, i, f) => { for (let k = 1; k <= MAX; k++) { const j = (i + k + MAX) % MAX, p = r.seats[j]; if (p && f(p)) return j } return -1 };
const put = (p, a) => { a = Math.min(a, p.chips); p.chips -= a; p.bet += a; p.tot += a; if (!p.chips) p.allin = true; return a };
const fixHost = r => { if (!r.seats.some(p => p && p.id === r.host)) { const p = r.seats.find(Boolean); r.host = p ? p.id : null } };
const clean = p => Object.assign(p, { in: false, hole: [], bet: 0, tot: 0, fold: false, allin: false, acted: false, shown: false });
const genCode = () => { let c; do { c = Array.from({ length: 5 }, () => 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'[crypto.randomInt(32)]).join('') } while (rooms.has(c)); return c };
function mkRoom() {
  const code = genCode();
  const r = {
    code, seats: Array(MAX).fill(null), host: null, chat: [], hist: [], log: [], phase: 'wait', board: [], dealer: -1, turn: -1,
    bet: 0, minRaise: 0, hands: 0, t0: 0, lvl: 0, timer: null, dl: 0, last: Date.now()
  };
  rooms.set(code, r); return r
}

function view(r, me) {
  const pl = r.seats[me], on = r.phase !== 'wait';
  return {
    code: r.code, phase: r.phase, you: me, rebuy: REBUY, hand: r.hands, host: !!pl && pl.id === r.host, board: r.board.map(cs),
    pot: on ? r.seats.reduce((a, p) => a + (p ? p.tot : 0), 0) : 0, bet: r.bet, minRaise: r.minRaise, turn: r.turn, dealer: r.dealer,
    dl: r.dl ? r.dl - Date.now() : 0, blinds: LEVELS[r.lvl],
    next: r.t0 && r.lvl < LEVELS.length - 1 ? r.t0 + (r.lvl + 1) * LEVEL_MS - Date.now() : 0,
    seats: r.seats.map((p, i) => p && {
      nick: p.nick, chips: p.chips, bet: p.bet, fold: p.fold, allin: p.allin, on: p.on, in: p.in,
      cards: i === me && p.hole.length ? p.hole.map(cs) : p.shown && !p.fold ? p.hole.map(cs) : p.in && !p.fold ? ['??', '??'] : []
    }),
    chat: r.chat.slice(-40), log: r.log.slice(-30), hist: r.hist
  };
}
function send(r) {
  r.last = Date.now();
  r.seats.forEach((p, i) => { if (p && p.ws && p.ws.readyState === 1) p.ws.send(JSON.stringify({ t: 's', s: view(r, i) })) })
}

/* ---------- 게임 진행 ---------- */
function startHand(r) {
  clearTimeout(r.timer);
  r.seats.forEach((p, i) => { if (p && p.leave) r.seats[i] = null }); fixHost(r);
  const ps = r.seats.filter(p => p && p.chips > 0);
  if (ps.length < 2) { r.seats.forEach(p => p && clean(p)); r.board = []; r.phase = 'wait'; r.turn = -1; return send(r) }
  r.seats.forEach(p => { if (p && p.chips <= 0) clean(p) });
  const lvl = Math.min(Math.floor((Date.now() - r.t0) / LEVEL_MS), LEVELS.length - 1);
  if (lvl > r.lvl) { r.lvl = lvl; note(r, `⬆ 블라인드 상승 ${LEVELS[lvl].join('/')}`) }
  const [sb, bb] = LEVELS[r.lvl];
  ps.forEach(p => Object.assign(p, { in: true, hole: [], bet: 0, tot: 0, fold: false, allin: false, acted: false, shown: false }));
  r.dealer = nextIdx(r, r.dealer, p => p.in);
  r.deck = mkDeck(); r.board = []; r.hands++; r.phase = 'preflop';
  ps.forEach(p => p.hole = [r.deck.pop(), r.deck.pop()]);
  const si = ps.length === 2 ? r.dealer : nextIdx(r, r.dealer, p => p.in), bi = nextIdx(r, si, p => p.in);
  put(r.seats[si], sb); put(r.seats[bi], bb);
  r.bet = bb; r.minRaise = bb; r.turn = nextIdx(r, bi, canAct);
  note(r, `── 핸드 #${r.hands} ──`);
  step(r);
}
function step(r) {
  const lv = live(r);
  if (lv.length === 1) return award(r, lv[0]);
  const can = lv.filter(p => !p.allin);
  const over = can.every(p => p.acted && p.bet === r.bet) || (can.length < 2 && (!can.length || can[0].bet >= r.bet));
  if (over) return street(r);
  arm(r);
}
function arm(r) {
  clearTimeout(r.timer); const i = r.turn, p = r.seats[i];
  const ms = p.leave ? 1500 : p.on ? TURN_MS : 8000; r.dl = Date.now() + ms;
  r.timer = setTimeout(() => act(r, i, p.bet >= r.bet ? 'call' : 'fold'), ms);
  send(r);
}
function street(r) {
  r.seats.forEach(p => { if (p) { p.bet = 0; p.acted = false } });
  r.bet = 0; r.minRaise = LEVELS[r.lvl][1];
  const nx = { preflop: 'flop', flop: 'turn', turn: 'river', river: 'show' }[r.phase];
  if (nx === 'show') return showdown(r);
  r.phase = nx; for (let i = nx === 'flop' ? 3 : 1; i > 0; i--)r.board.push(r.deck.pop());
  r.turn = nextIdx(r, r.dealer, canAct);
  step(r);
}
function act(r, i, type, amt) {
  const p = r.seats[i];
  if (!p || i !== r.turn || !['preflop', 'flop', 'turn', 'river'].includes(r.phase)) return;
  const need = r.bet - p.bet, prev = r.bet; let to = 0;
  if (type === 'raise') {
    to = Math.min(Math.floor(+amt) || 0, p.bet + p.chips);
    if (to <= r.bet) type = 'call';
    else if (to < r.bet + r.minRaise && to < p.bet + p.chips) return; // 최소 레이즈 미달
  }
  clearTimeout(r.timer);
  if (type === 'fold') { p.fold = true; note(r, `${p.nick} 폴드`) }
  else if (type === 'call') { const a = put(p, need); p.acted = true; note(r, need > 0 ? `${p.nick} 콜 ${a}${p.allin ? ' (올인)' : ''}` : `${p.nick} 체크`) }
  else {
    const d = to - r.bet; put(p, to - p.bet); if (d >= r.minRaise) r.minRaise = d; r.bet = to;
    r.seats.forEach(q => { if (q && q !== p) q.acted = false }); p.acted = true;
    note(r, `${p.nick} ${prev ? '레이즈' : '벳'} ${to}${p.allin ? ' (올인)' : ''}`);
  }
  r.turn = nextIdx(r, i, canAct);
  step(r);
}
function award(r, w) { const pot = r.seats.reduce((a, p) => a + (p ? p.tot : 0), 0); w.chips += pot; finish(r, [[w, pot, '']]) }
function showdown(r) {
  const lv = live(r), all = r.seats.filter(p => p && p.in);
  lv.forEach(p => { p.sc = best([...p.hole, ...r.board]); p.shown = true });
  const win = new Map(); let prev = 0;
  for (const L of [...new Set(lv.map(p => p.tot))].sort((a, b) => a - b)) { // 메인/사이드 팟
    const pot = all.reduce((a, p) => a + Math.min(p.tot, L) - Math.min(p.tot, prev), 0); prev = L;
    const el = lv.filter(p => p.tot >= L), m = Math.max(...el.map(p => p.sc)), ws = el.filter(p => p.sc === m);
    const sh = Math.floor(pot / ws.length), rem = pot - sh * ws.length;
    ws.forEach((p, k) => win.set(p, (win.get(p) || 0) + sh + (k < rem ? 1 : 0)));
  }
  finish(r, [...win].map(([p, a]) => { p.chips += a; return [p, a, HAND[Math.floor(p.sc / 15 ** 5)]] }));
}
function finish(r, res) {
  clearTimeout(r.timer); r.phase = 'show'; r.turn = -1; r.dl = 0;
  const w = res.map(([p, a, h]) => `${p.nick} +${a}${h ? ` (${h})` : ''}`);
  note(r, '🏆 ' + w.join(', '));
  r.hist.unshift({ n: r.hands, board: r.board.map(cs), w }); if (r.hist.length > 30) r.hist.pop();
  send(r); r.timer = setTimeout(() => startHand(r), NEXT_MS);
}

/* ---------- 웹소켓 ---------- */
wss.on('connection', ws => {
  let r = null, me = -1;
  const err = m => ws.send(JSON.stringify({ t: 'err', m }));
  ws.on('message', raw => {
    let m; try { m = JSON.parse(raw) } catch { return }
    if (m.t === 'create' || m.t === 'join') {
      const nick = String(m.nick || '').trim().slice(0, 10), pid = String(m.pid || '').slice(0, 40);
      if (!nick || !pid) return err('닉네임을 입력하세요');
      r = m.t === 'create' ? mkRoom() : rooms.get(String(m.room || '').toUpperCase());
      if (!r) return err('방을 찾을 수 없어요');
      me = r.seats.findIndex(p => p && p.id === pid);
      if (me < 0) {
        me = r.seats.findIndex(p => !p);
        if (me < 0) { r = null; return err('방이 가득 찼어요 (6/6)') }
        r.seats[me] = { id: pid, nick, chips: START_CHIPS, hole: [], bet: 0, tot: 0, rebuys: 0 };
        if (!r.host) r.host = pid; note(r, `${nick} 입장`);
      }
      const p = r.seats[me]; p.ws = ws; p.on = true; p.leave = false;
      ws.send(JSON.stringify({ t: 'joined', room: r.code })); send(r);
      if (r.phase === 'wait' && r.t0 && r.seats.filter(q => q && q.chips > 0).length > 1) startHand(r); return;
    }
    const p = r && r.seats[me]; if (!p) return;
    if (m.t === 'chat') {
      const x = String(m.x || '').trim().slice(0, 200);
      if (x) { r.chat.push({ n: p.nick, x }); if (r.chat.length > 100) r.chat.shift(); send(r) }
    }
    else if (m.t === 'act') act(r, me, m.a, m.amt);
    else if (m.t === 'start' && p.id === r.host && r.phase === 'wait' && r.seats.filter(q => q && q.chips > 0).length > 1) {
      if (!r.t0) r.t0 = Date.now(); startHand(r)
    }
    else if (m.t === 'rebuy' && p.chips <= 0 && !(p.in && ['preflop', 'flop', 'turn', 'river'].includes(r.phase))) {
      p.chips = REBUY; p.rebuys++; note(r, `${p.nick} 칩 ${REBUY} 다시 받음`);
      if (r.phase === 'wait' && r.t0 && r.seats.filter(q => q && q.chips > 0).length > 1) startHand(r); else send(r);
    }
    else if (m.t === 'leave') {
      note(r, `${p.nick} 퇴장`);
      if (r.phase === 'wait' || r.phase === 'show' || !p.in) { r.seats[me] = null; fixHost(r); send(r) }
      else { p.leave = true; p.on = false; if (r.turn === me) arm(r); else send(r) }
    }
  });
  ws.on('close', () => { const p = r && r.seats[me]; if (p && p.ws === ws) { p.on = false; send(r) } });
});
setInterval(() => { for (const [c, r] of rooms) if (Date.now() - r.last > 36e5 && !r.seats.some(p => p && p.on)) { clearTimeout(r.timer); rooms.delete(c) } }, 6e4);
server.listen(PORT, () => console.log('http://localhost:' + PORT));
