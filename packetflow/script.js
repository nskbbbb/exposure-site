'use strict';
/* ===== PacketFlow: engine (graph, routing, Dijkstra, event-driven Sim) – no DOM use ===== */
const ip2n=s=>{const p=String(s).trim().split('.');if(p.length!=4||p.some(x=>!/^\d+$/.test(x)||+x>255))return null;return +p[0]*16777216+(+p[1]<<16)+(+p[2]<<8)+(+p[3])};
const n2ip=n=>[n>>>24,n>>>16&255,n>>>8&255,n&255].join('.');
const plen=m=>{const n=ip2n(m);if(n==null)return null;const b=n.toString(2).padStart(32,'0');return/^1*0*$/.test(b)?(b.indexOf('0')<0?32:b.indexOf('0')):null};
const parseCidr=s=>{const m=/^(\d+\.\d+\.\d+\.\d+)\/(\d+)$/.exec(String(s).trim());if(!m)return null;const n=ip2n(m[1]),l=+m[2];return n==null||l>32?null:{n,l}};
const inNet=(n,c)=>c.l==0||(n>>>(32-c.l))==(c.n>>>(32-c.l));
const TYPES={pc:'PC',router:'RTR',switch:'SW',server:'SRV',firewall:'FW'};
const newSt=()=>({n:0,sent:0,deliv:0,drop:0,bytes:0,clk:0,lat:[],proto:{},pk:[],log:[],hist:[],dev:{}});
let N,st=newSt(),sim,timer=null,sel=null,tool=null,pend=null,flt='ALL',selp=null,C={kind:'ping',port:''},RT={},LAB={act:0,bk:''},cfg={speed:700,anim:true};
const dev=id=>N.devs.find(d=>d.id==id),linkOf=(a,b)=>N.links.find(l=>(l.a==a&&l.b==b)||(l.a==b&&l.b==a)),ifAt=(l,id)=>l.a==id?l.ia:l.ib;
const primary=d=>(d.ifaces.find(f=>ip2n(f.ip)!=null)||{}).ip||'';
const owner=ip=>{for(const d of N.devs){const i=d.ifaces.findIndex(f=>f.ip==ip);if(i>=0)return{d,i}}return null};
function addIf(d){d.ifaces.push({name:'eth'+d.ifaces.length,ip:'',mask:'255.255.255.0',mac:'00:1A:'+(N.seq++).toString(16).padStart(8,'0').match(/../g).join(':')})}
function addDev(type,x,y,o={}){const d={id:'d'+(N.seq++),type,name:o.name||TYPES[type]+(N.devs.filter(v=>v.type==type).length+1),x,y,ifaces:[],routes:[],fw:[],gw:'',ttl:64};for(let i=0;i<{pc:1,server:1,router:2,firewall:2,switch:0}[type];i++)addIf(d);N.devs.push(d);return d}
const used=(d,i)=>N.links.some(l=>(l.a==d.id&&l.ia==i)||(l.b==d.id&&l.ib==i));
function pick(d){if(d.type=='switch')return -1;let i=d.ifaces.findIndex((_,k)=>!used(d,k));if(i<0&&(d.type=='router'||d.type=='firewall')){addIf(d);i=d.ifaces.length-1}return i<0?null:i}
function connect(a,b){if(a==b)return'Pick two different devices';if(linkOf(a.id,b.id))return'Those devices are already cabled';const ia=pick(a),ib=pick(b);if(ia===null||ib===null)return(ia===null?a.name:b.name)+' has no free interface';N.links.push({id:'l'+(N.seq++),a:a.id,b:b.id,ia,ib,up:true,lat:2});return''}
function sample(){N={devs:[],links:[],seq:1};const A=(t,x,y,n,ip,gw)=>{const d=addDev(t,x,y,{name:n});if(ip)d.ifaces[0].ip=ip;if(gw)d.gw=gw;return d};
 const p1=A('pc',80,110,'PC1','192.168.1.10','192.168.1.1'),p2=A('pc',80,260,'PC2','192.168.1.11','192.168.1.1'),p3=A('pc',80,410,'PC3','192.168.1.12','192.168.1.1');
 const s1=A('switch',230,260,'SW1'),r=A('router',380,260,'R1'),fw=A('firewall',540,260,'FW1'),s2=A('switch',690,260,'SW2'),sv=A('server',830,260,'WebServer','10.0.1.10','10.0.1.1');
 r.ifaces[0].ip='192.168.1.1';r.ifaces[1].ip='10.0.0.1';fw.ifaces[0].ip='10.0.0.2';fw.ifaces[1].ip='10.0.1.1';
 r.routes.push({net:'10.0.1.0/24',via:'10.0.0.2'});fw.routes.push({net:'192.168.1.0/24',via:'10.0.0.1'});fw.fw.push({a:'deny',pr:'tcp',port:'23'});
 [[p1,s1],[p2,s1],[p3,s1],[s1,r],[r,fw],[fw,s2],[s2,sv]].forEach(([a,b])=>connect(a,b))}
function dijkstra(s,t,ok=()=>true){const dist={[s]:0},prev={},q=new Set([s]),done=new Set();
 while(q.size){let u=null;for(const x of q)if(u===null||dist[x]<dist[u])u=x;q.delete(u);if(u==t)break;done.add(u);if(u!=s&&!ok(dev(u)))continue;
  for(const l of N.links){if(!l.up)continue;const v=l.a==u?l.b:l.b==u?l.a:null;if(!v||done.has(v))continue;const nd=dist[u]+(+l.lat||1);if(dist[v]===undefined||nd<dist[v]){dist[v]=nd;prev[v]=u;q.add(v)}}}
 if(dist[t]===undefined)return null;const p=[t];while(p[0]!=s)p.unshift(prev[p[0]]);return p}
const pathCost=p=>p.slice(1).reduce((c,x,i)=>c+(+linkOf(p[i],x).lat||1),0);
function routesOf(d){const r=[];d.ifaces.forEach((f,i)=>{const m=plen(f.mask),a=ip2n(f.ip);if(a!=null&&m!=null)r.push({net:n2ip((a&ip2n(f.mask))>>>0)+'/'+m,via:'',ifi:i,kind:'connected'})});d.routes.forEach(x=>r.push({...x,kind:'static'}));if(d.gw)r.push({net:'0.0.0.0/0',via:d.gw,kind:'default'});return r}
function lookup(d,dip){const n=ip2n(dip);let best=null;for(const r of routesOf(d)){const c=parseCidr(r.net);if(c&&inNet(n,c)&&(!best||c.l>best.c.l))best={r,c}}if(!best)return null;
 const r=best.r;let ifi=r.ifi;if(r.via){const v=ip2n(r.via);ifi=d.ifaces.findIndex(f=>{const a=ip2n(f.ip),m=ip2n(f.mask);return a!=null&&m!=null&&v!=null&&((a&m)>>>0)==((v&m)>>>0)});if(ifi<0)return{err:`${d.name}: next hop ${r.via} is not on any connected subnet (check IP, mask and gateway)`}}return{r,c:best.c,nh:r.via||dip,ifi}}
const SC={ping:()=>[[1,'ICMP','ICMP','Echo (ping) request',74],[0,'ICMP','ICMP','Echo (ping) reply',74]],
 tcp:()=>[[1,'TCP','TCP','SYN',60,'SYN'],[0,'TCP','TCP','SYN-ACK',60,'SYN, ACK'],[1,'TCP','TCP','ACK',54,'ACK']],
 udp:()=>[[1,'UDP','UDP','UDP datagram (no handshake)',82],[0,'UDP','UDP','UDP datagram reply',82]],
 arp:()=>[[1,'ARP','ARP','Who has {d}? Tell {s}',42,'request'],[0,'ARP','ARP','{d} is at {dm}',42,'reply']],
 dns:()=>[[1,'DNS','UDP','Standard query A web.packetflow.lab',74],[0,'DNS','UDP','Response: web.packetflow.lab A {d}',90]],
 http:()=>[...SC.tcp(),[1,'HTTP','TCP','GET /index.html HTTP/1.1',380,'PSH, ACK'],[0,'HTTP','TCP','HTTP/1.1 200 OK (text/html)',1240,'PSH, ACK'],[1,'TCP','TCP','ACK',54,'ACK']]};
const DP={tcp:80,udp:7,dns:53,http:80};
class Sim{
 constructor(s){this.s=s;this.q=[];this.onHop=null}
 log(m,l){this.s.log.push({t:+this.s.clk.toFixed(1),m,l:l||'info'});if(this.s.log.length>300)this.s.log.shift()}
 mk(o){const s=this.s,p={id:++s.n,status:'in flight',path:[],hops:[],lat:0,...o};p.ttl0=p.ttl;s.pk.push(p);s.sent++;s.proto[p.proto]=(s.proto[p.proto]||0)+1;return p}
 send(d,p){p.path.push(d.id);this.log(`#${p.id} ${p.proto} ${p.info} · ${d.name} → ${p.dip}`);this.q.push({p,at:d.id})}
 start(a,b,kind,port){if(a==b)return'Choose two different devices';const sip=primary(a),dip=primary(b);if(!sip)return a.name+' has no valid IP address';if(!dip)return b.name+' has no valid IP address';
  const steps=SC[kind](),pt=+port||DP[kind]||0,sp=49152+this.s.n%1000,bm=b.ifaces.find(f=>f.ip==dip).mac;let i=0;
  const go=()=>{if(i>=steps.length)return;const[c,proto,tr,info,size,fl]=steps[i++],x=c?a:b,y=c?b:a,port_=tr=='TCP'||tr=='UDP';
   const p=this.mk({proto,tr,sip:primary(x),dip:primary(y),sport:port_?(c?sp:pt):'',dport:port_?(c?pt:sp):'',size,flags:fl||'',info:info.replace('{d}',dip).replace('{s}',sip).replace('{dm}',bm),ttl:+x.ttl||64,bc:proto=='ARP'&&!!c});p.after=go;this.send(x,p)};
  go();return''}
 step(){const e=this.q.shift();if(!e)return false;this.handle(e);return true}
 drop(p,d,w){const s=this.s;p.status='dropped';p.why=w;p.at=d.name;s.drop++;s.hist.push([s.deliv,s.drop]);this.log(`#${p.id} DROPPED at ${d.name}: ${w}`,'bad')}
 deliver(p,d){const s=this.s;p.status='delivered';s.deliv++;s.bytes+=p.size;s.lat.push(p.lat);s.hist.push([s.deliv,s.drop]);this.log(`#${p.id} ${p.proto} delivered to ${d.name} (${p.lat} ms)`,'ok');p.after&&p.after()}
 hop(p,a,b,l,n){const s=this.s;s.clk+=+l.lat||1;p.lat+=+l.lat||1;p.path.push(b);s.dev[b]=(s.dev[b]||0)+1;this.q.push({p,...n});this.onHop&&this.onHop(a,b,l,p)}
 handle(e){const p=e.p,d=dev(e.at);if(!d){p.status='dropped';p.why='device removed';return}if(!e.seg)return this.egress(p,d);
  if(e.si<e.seg.length-1){const nx=e.seg[e.si+1],l=linkOf(e.at,nx);if(!l||!l.up)return this.drop(p,d,`Link ${d.name}–${dev(nx)?.name} is down`);return this.hop(p,e.at,nx,l,{seg:e.seg,si:e.si+1,at:nx})}
  this.ingress(p,d)}
 ingress(p,d){
  if(d.ifaces.some(f=>f.ip&&f.ip==p.dip))return this.deliver(p,d);
  if(p.proto=='ARP')return this.drop(p,d,`ARP reached ${d.name}, which does not own ${p.dip}`);
  if(d.type!='router'&&d.type!='firewall')return this.drop(p,d,`${d.name} is an end host/switch and does not forward packets for ${p.dip}`);
  if(--p.ttl<=0)return this.drop(p,d,`TTL expired in transit at ${d.name} (initial TTL ${p.ttl0})`);
  if(d.type=='firewall'){const i=d.fw.findIndex(r=>(r.pr=='any'||r.pr==p.tr.toLowerCase())&&(!r.port||r.port==p.dport||r.port==p.sport));if(i>=0&&d.fw[i].a=='deny')return this.drop(p,d,`Firewall ${d.name} blocked ${p.tr}${p.dport?' port '+p.dport:''} (rule ${i+1})`)}
  this.egress(p,d)}
 egress(p,d){const L=lookup(d,p.dip);
  if(!L)return this.drop(p,d,`No route to ${p.dip} on ${d.name}`+(d.type=='pc'||d.type=='server'?' – set a default gateway':' – add a static route'));
  if(L.err)return this.drop(p,d,L.err);
  if(p.proto=='ARP'&&L.r.kind!='connected')return this.drop(p,d,`ARP target ${p.dip} is not on the local subnet`);
  const f=d.ifaces[L.ifi],o=owner(L.nh);
  if(!o)return this.drop(p,d,`ARP failed: nothing answers for ${L.nh} (check IP addresses and gateway)`);
  if(o.d==d)return this.drop(p,d,'Next hop is this device itself');
  const seg=dijkstra(d.id,o.d.id,x=>x.type=='switch');
  if(!seg)return this.drop(p,d,`${o.d.name} is unreachable from ${d.name}: no working cable path (disconnected link?)`);
  const l1=linkOf(seg[0],seg[1]),l2=linkOf(seg[seg.length-2],seg[seg.length-1]);
  if(ifAt(l1,d.id)!=L.ifi||ifAt(l2,o.d.id)!=o.i)return this.drop(p,d,`${d.name} ${f.name} and ${o.d.name} are not on the same Layer-2 segment`);
  p.hops.push({a:d.name,b:o.d.name,sm:f.mac,dm:p.bc?'ff:ff:ff:ff:ff:ff':o.d.ifaces[o.i].mac});
  this.hop(p,d.id,seg[1],l1,{seg,si:1,at:seg[1]})}
}
function runQuiet(a,b,kind,port){const q=new Sim(newSt()),r=q.start(a,b,kind,port);let n=0;while(q.step()&&n++<500);return{q,err:r,pk:q.s.pk,bad:q.s.pk.find(p=>p.status!='delivered')}}

/* ===== UI ===== */
const $=s=>document.querySelector(s),NS='http://www.w3.org/2000/svg',R={},pct=(a,b)=>(a/b*100).toFixed(0)+'%',avg=a=>a.reduce((x,y)=>x+y,0)/a.length;
const h=(t,a={},...c)=>{const e=document.createElement(t);for(const k in a)k.startsWith('on')?e[k]=a[k]:e.setAttribute(k,a[k]);c.flat().forEach(x=>e.append(x));return e};
const S=(t,a={},x)=>{const e=document.createElementNS(NS,t);for(const k in a)e.setAttribute(k,a[k]);if(x!=null)e.textContent=x;return e};
const view=()=>{const v=$('#view');v.innerHTML='';return v},msg=m=>{const e=$('#msg');if(e)e.textContent=m};
const touch=()=>{if(!LAB.act)try{localStorage.setItem('packetflow.project',JSON.stringify(N))}catch(e){}};
function fixC(){const l3=N.devs.filter(d=>d.type!='switch');if(!dev(C.src))C.src=(l3.find(d=>d.type=='pc')||l3[0]||{}).id;if(!dev(C.dst))C.dst=(l3.find(d=>d.type=='server')||l3[1]||{}).id}
function resetSim(){pause();st=newSt();sim=new Sim(st);sim.onHop=anim;document.querySelectorAll('.pkt').forEach(e=>e.remove());setState()}
function run(){if(timer)return;timer=setInterval(()=>{if(!sim.step())pause();refresh()},cfg.speed);setState()}
function pause(){clearInterval(timer);timer=null;setState()}
function queue(){fixC();const r=sim.start(dev(C.src),dev(C.dst),C.kind,C.port);if(r){msg(r);alert(r)}else run();refresh()}
function setState(){const e=$('#state');if(e)e.textContent=timer?'● Running':sim.q.length?`⏸ Paused · ${sim.q.length} queued`:'Idle'}
const UP={dashboard:()=>R.dashboard(),analyzer:()=>R.analyzer(),monitor:()=>R.monitor(),console:()=>cu()};
function refresh(){setState();UP[cur]&&UP[cur]()}
let cur='dashboard';
const PG=[['dashboard','Dashboard'],['studio','Network Studio'],['config','Device Configuration'],['console','Simulation Console'],['analyzer','Packet Analyzer'],['routing','Routing Tables'],['monitor','Network Monitor'],['lab','Troubleshooting Lab'],['docs','Documentation'],['settings','Settings']];
const go=id=>location.hash=='#'+id?render():location.hash=id;
function render(){cur=location.hash.slice(1);if(!R[cur])cur='dashboard';tool=null;pend=null;PG.forEach(([id])=>$('#n-'+id).classList.toggle('on',id==cur));$('#title').textContent=PG.find(p=>p[0]==cur)[1];R[cur]();setState()}
const COL={TCP:'#38bdf8',HTTP:'#34d399',UDP:'#fbbf24',ICMP:'#a78bfa',ARP:'#f472b6',DNS:'#fb923c'};
function anim(a,b,p){if(!cfg.anim)return;const A=dev(a),B=dev(b),T=Math.max(150,cfg.speed*.85);document.querySelectorAll('svg.topo').forEach(sv=>{const c=S('circle',{r:7,fill:COL[p.proto]||'#fff',class:'pkt'});sv.append(c);const t0=performance.now();(function f(t){const k=Math.min(1,(t-t0)/T);c.setAttribute('cx',A.x+(B.x-A.x)*k);c.setAttribute('cy',A.y+(B.y-A.y)*k);k<1?requestAnimationFrame(f):c.remove()})(t0)})}
function drawTopo(sv,edit,hl=[]){sv.innerHTML='';sv.setAttribute('viewBox','0 0 900 520');sv.setAttribute('class','topo');if(edit)sv.onpointerdown=()=>{sel=null;redraw()};
 N.links.forEach(l=>{const A=dev(l.a),B=dev(l.b),a={x1:A.x,y1:A.y,x2:B.x,y2:B.y};sv.append(S('line',{...a,class:'lk'+(l.up?'':' down')+(hl.includes(l.id)?' hl':'')+(sel&&sel.id==l.id?' sel':'')}));
  if(edit){const t=S('line',{...a,class:'hit'});t.onpointerdown=e=>{e.stopPropagation();sel={id:l.id,k:'l'};redraw()};sv.append(t)}
  sv.append(S('text',{x:(A.x+B.x)/2,y:(A.y+B.y)/2-6,class:'s'},l.up?l.lat+' ms':'DOWN'))});
 N.devs.forEach(d=>{const r=S('rect',{x:d.x-34,y:d.y-22,width:68,height:44,rx:8,class:'dv '+d.type+(hl.includes(d.id)?' hl':'')+(sel&&sel.id==d.id?' sel':'')});if(edit)r.onpointerdown=e=>devDown(e,d,sv);
  sv.append(r,S('text',{x:d.x,y:d.y+5},TYPES[d.type]),S('text',{x:d.x,y:d.y+38},d.name),S('text',{x:d.x,y:d.y+51,class:'s'},primary(d)||(d.type=='switch'?'L2':'no IP')))})}
function devDown(e,d,sv){e.stopPropagation();
 if(tool=='link'){if(!pend){pend=d;msg('Now click the second device')}else{const r=connect(pend,d);pend=null;msg(r||'Cable added');if(!r)touch()}redraw();return}
 sel={id:d.id,k:'d'};redraw();const mv=ev=>{const p=sv.createSVGPoint();p.x=ev.clientX;p.y=ev.clientY;const q=p.matrixTransform(sv.getScreenCTM().inverse());d.x=Math.max(40,Math.min(860,q.x));d.y=Math.max(30,Math.min(480,q.y));drawTopo(sv,true)};
 const up=()=>{removeEventListener('pointermove',mv);removeEventListener('pointerup',up);touch()};addEventListener('pointermove',mv);addEventListener('pointerup',up)}
function fld(lab,o,k,cb,chk,ro){const i=h('input',{value:o[k]??''});if(ro)i.readOnly=true;if(chk)i.classList.toggle('bad',!chk(i.value));i.onchange=()=>{o[k]=i.value.trim();cb()};return h('label',{class:'f'},lab,i)}
const okIp=v=>!v||ip2n(v)!=null;
function devForm(d,cb){const w=h('div'),rp=()=>{touch();cb()};w.append(h('h3',{},d.type+' · device settings'),fld('Name',d,'name',rp));
 if(d.type=='pc'||d.type=='server')w.append(fld('Default gateway',d,'gw',rp,okIp),fld('Initial TTL',d,'ttl',rp));
 if(d.type=='switch')w.append(h('p',{class:'m'},'Layer-2 switch: forwards frames between cabled devices. No IP configuration.'));
 else d.ifaces.forEach((f,i)=>{const l=N.links.find(l=>(l.a==d.id&&l.ia==i)||(l.b==d.id&&l.ib==i));w.append(h('div',{class:'if'},h('b',{},f.name+' – '+(l?'to '+dev(l.a==d.id?l.b:l.a).name+(l.up?'':' (DOWN)'):'not cabled')),fld('IP address',f,'ip',rp,okIp),fld('Subnet mask',f,'mask',rp,v=>plen(v)!=null),fld('MAC address',f,'mac',rp,null,1)))});
 if(d.type!='switch'){const nn=h('input',{placeholder:'10.0.1.0/24'}),vv=h('input',{placeholder:'next hop IP'});w.append(h('h3',{},'Static routes'),...d.routes.map((r,i)=>h('div',{class:'rt'},r.net+' via '+r.via,h('button',{onclick:()=>{d.routes.splice(i,1);rp()}},'Remove'))),
  h('div',{class:'rt'},nn,vv,h('button',{onclick:()=>{if(!parseCidr(nn.value)||ip2n(vv.value)==null)return alert('Enter a network in CIDR form (10.0.1.0/24) and a valid next-hop IP.');d.routes.push({net:nn.value.trim(),via:vv.value.trim()});rp()}},'Add route')))}
 if(d.type=='firewall'){const ac=h('select',{},h('option',{},'deny'),h('option',{},'allow')),pr=h('select',{},...['tcp','udp','icmp','any'].map(x=>h('option',{},x))),po=h('input',{placeholder:'port (blank = any)'});
  w.append(h('h3',{},'Firewall rules (first match wins, default allow)'),...d.fw.map((r,i)=>h('div',{class:'rt'},`${i+1}. ${r.a} ${r.pr} ${r.port||'any port'}`,h('button',{onclick:()=>{d.fw.splice(i,1);rp()}},'Remove'))),h('div',{class:'rt'},ac,pr,po,h('button',{onclick:()=>{d.fw.push({a:ac.value,pr:pr.value,port:po.value.trim()});rp()}},'Add rule')))}
 return w}
function panel(pn){pn.innerHTML='';if(!sel)return pn.append(h('h3',{},'Properties'),h('p',{class:'m'},'Select a device or cable. Drag devices to move them. Use Cable to connect two devices.'));
 if(sel.k=='d'){const d=dev(sel.id);if(!d){sel=null;return panel(pn)}pn.append(devForm(d,redraw))}
 else{const l=N.links.find(x=>x.id==sel.id);if(!l){sel=null;return panel(pn)}const A=dev(l.a),B=dev(l.b);pn.append(h('h3',{},'Cable'),h('p',{},`${A.name} (${A.ifaces[l.ia]?.name||'L2'}) ↔ ${B.name} (${B.ifaces[l.ib]?.name||'L2'})`),fld('Latency (ms)',l,'lat',()=>{l.lat=Math.max(1,+l.lat||1);touch();redraw()}),h('button',{onclick:()=>{l.up=!l.up;touch();redraw()}},l.up?'Disconnect (simulate failure)':'Reconnect'))}}
let redraw=()=>{};
R.studio=()=>{const v=view(),sv=S('svg',{}),pn=h('div',{class:'card'});
 const add=t=>h('button',{onclick:()=>{const d=addDev(t,100+Math.random()*700|0,60+Math.random()*400|0);sel={id:d.id,k:'d'};touch();redraw()}},'+ '+TYPES[t]);
 v.append(h('div',{class:'bar'},...Object.keys(TYPES).map(add),h('button',{onclick:e=>{tool=tool?null:'link';pend=null;e.target.classList.toggle('pri',!!tool);msg(tool?'Cable mode: click two devices':'')}},'Cable'),
  h('button',{onclick:()=>{if(!sel)return;if(sel.k=='d'){N.links=N.links.filter(l=>l.a!=sel.id&&l.b!=sel.id);N.devs=N.devs.filter(d=>d.id!=sel.id)}else N.links=N.links.filter(l=>l.id!=sel.id);sel=null;touch();redraw()}},'Delete selected'),h('span',{id:'msg',class:'m'})),h('div',{class:'split'},sv,pn));
 redraw=()=>{drawTopo(sv,true);panel(pn)};redraw()};
R.config=()=>{const v=view(),d=sel&&sel.k=='d'&&dev(sel.id)||N.devs[0];sel={id:d.id,k:'d'};
 v.append(h('div',{class:'split'},h('div',{class:'card'},h('h3',{},'All devices'),h('table',{},h('thead',{},h('tr',{},...['Name','Type','IP addresses','Gateway'].map(x=>h('th',{},x)))),h('tbody',{},...N.devs.map(x=>h('tr',{class:x==d?'sel':'',onclick:()=>{sel={id:x.id,k:'d'};R.config()}},h('td',{},x.name),h('td',{},x.type),h('td',{},x.ifaces.map(f=>f.ip).filter(Boolean).join(', ')||'–'),h('td',{},x.gw||'–')))))),h('div',{class:'card'},devForm(d,R.config))))};
const logList=a=>h('div',{class:'log'},a.length?a.map(e=>h('div',{class:'lg '+e.l},`[${e.t} ms] ${e.m}`)):'No activity yet. Send a packet from the Simulation Console.');
function line(w,hh,sets){const c=h('canvas',{width:w,height:hh}),x=c.getContext('2d'),mx=Math.max(1,...sets.flatMap(s=>s.d));x.font='11px sans-serif';
 for(let i=0;i<=4;i++){const y=10+(hh-30)*i/4;x.strokeStyle='#24324f';x.beginPath();x.moveTo(34,y);x.lineTo(w-6,y);x.stroke();x.fillStyle='#8296b8';x.fillText((mx*(1-i/4)).toFixed(mx<10?1:0),2,y+3)}
 sets.forEach(s=>{x.strokeStyle=s.c;x.lineWidth=2;x.beginPath();s.d.forEach((v,i)=>{const X=34+(w-40)*(s.d.length<2?0:i/(s.d.length-1)),Y=10+(hh-30)*(1-v/mx);i?x.lineTo(X,Y):x.moveTo(X,Y)});x.stroke()});return c}
function bars(w,hh,items){const c=h('canvas',{width:w,height:hh}),x=c.getContext('2d'),mx=Math.max(1,...items.map(i=>i[1])),bw=(w-20)/Math.max(items.length,1);x.font='11px sans-serif';
 items.forEach(([k,n],i)=>{const bh=(hh-40)*n/mx;x.fillStyle=COL[k]||'#38bdf8';x.fillRect(14+i*bw+6,hh-20-bh,bw-12,bh);x.fillStyle='#8296b8';x.fillText(k,14+i*bw+6,hh-6);x.fillText(n,14+i*bw+6,hh-24-bh)});return c}
function demo(){fixC();const p=N.devs.find(d=>d.type=='pc'),s=N.devs.find(d=>d.type=='server');if(!p||!s)return alert('Add a PC and a server first.');C={src:p.id,dst:s.id,kind:'http',port:''};go('console');queue()}
R.dashboard=()=>{const v=view(),s=st,tot=s.deliv+s.drop,up=N.links.filter(l=>l.up).length;
 const cd=(t,n,sub,to)=>h('div',{class:'card click',onclick:()=>go(to)},h('h3',{},t),h('span',{class:'n'},n),h('span',{class:'m'},sub));
 v.append(h('div',{class:'grid'},cd('Network devices',N.devs.length,'in topology','studio'),cd('Active connections',up+' / '+N.links.length,'cables up','studio'),cd('Packets transmitted',s.sent,'simulated','analyzer'),cd('Packets dropped',s.drop,tot?pct(s.drop,tot)+' of completed':'none yet','analyzer'),cd('Network availability',tot?pct(s.deliv,tot):'n/a','packet delivery rate','monitor'),cd('Average latency',s.lat.length?avg(s.lat).toFixed(1)+' ms':'n/a','simulated, per packet','monitor')),
  h('div',{class:'bar',style:'margin-top:14px'},h('button',{class:'pri',onclick:demo},'Run demo: PC1 → web server (HTTP)')),
  h('div',{class:'row'},h('div',{class:'card'},h('h3',{},'Cumulative delivered (cyan) and dropped (red)'),line(560,200,[{d:s.hist.map(x=>x[0]),c:'#38bdf8'},{d:s.hist.map(x=>x[1]),c:'#f87171'}])),h('div',{class:'card'},h('h3',{},'Recent activity'),logList(s.log.slice(-10).reverse()))))};
const sl=(k,list)=>{const s=h('select',{},...list.map(([v,l])=>h('option',{value:v},l)));s.value=C[k];s.onchange=()=>C[k]=s.value;return s};
function toggles(after){return h('div',{},...N.links.map(l=>h('div',{class:'rt'},`${dev(l.a).name} ↔ ${dev(l.b).name}`,h('button',{class:l.up?'':'pri',onclick:()=>{l.up=!l.up;touch();after()}},l.up?'Disconnect':'Reconnect'))))}
function cu(){const a=$('#cs'),b=$('#clog');if(!a)return;a.innerHTML='';a.append(h('p',{},`Queued events: ${sim.q.length}`),h('p',{},`Simulated clock: ${st.clk.toFixed(1)} ms`),h('p',{},`Delivered ${st.deliv} · Dropped ${st.drop}`));b.replaceChildren(logList(st.log.slice(-40).reverse()))}
R.console=()=>{fixC();const v=view(),l3=N.devs.filter(d=>d.type!='switch').map(d=>[d.id,d.name+' ('+(primary(d)||'no IP')+')']),sv=S('svg',{}),pt=h('input',{placeholder:'port',value:C.port,style:'width:80px'});pt.onchange=()=>C.port=pt.value;
 v.append(h('div',{class:'bar'},sl('src',l3),'→',sl('dst',l3),sl('kind',[['ping','ICMP ping'],['tcp','TCP handshake'],['udp','UDP'],['arp','ARP'],['dns','DNS'],['http','HTTP']]),pt,h('button',{class:'pri',onclick:queue},'Send test packet'),h('button',{onclick:()=>{if(!sim.q.length)return msg('Nothing queued');run()}},'Start'),h('button',{onclick:pause},'Pause'),h('button',{onclick:()=>{if(sim.q.length)run()}},'Resume'),h('button',{onclick:()=>{pause();sim.step();refresh()}},'Step'),h('button',{onclick:()=>{resetSim();R.console()}},'Reset'),h('span',{id:'msg',class:'m'})),
  h('div',{class:'split'},sv,h('div',{class:'card'},h('h3',{},'Simulation state'),h('div',{id:'cs'}),h('h3',{},'Cables (click to fail or restore)'),toggles(R.console))),h('div',{class:'card'},h('h3',{},'Event log'),h('div',{id:'clog'})));drawTopo(sv,false);cu()};
const kv=(t,rows)=>h('div',{class:'card'},h('h3',{},t),h('table',{},...rows.map(([k,x])=>h('tr',{},h('th',{},k),h('td',{},String(x))))));
R.analyzer=()=>{const v=view(),rows=st.pk.filter(p=>flt=='ALL'||p.proto==flt||p.tr==flt),nm=id=>dev(id)?.name||'?';
 v.append(h('div',{class:'note'},'All packets here are SIMULATED by PacketFlow. Browsers cannot capture real network traffic, so nothing in this view comes from a real network.'),
  h('div',{class:'bar'},...['ALL','TCP','UDP','ICMP','ARP','DNS','HTTP'].map(f=>h('button',{class:flt==f?'pri':'',onclick:()=>{flt=f;R.analyzer()}},f))),
  h('div',{class:'card',style:'max-height:300px;overflow:auto'},h('table',{},h('thead',{},h('tr',{},...['No.','Source','Destination','Protocol','Src port','Dst port','Size','Status'].map(x=>h('th',{},x)))),h('tbody',{},...rows.map(p=>h('tr',{class:p.id==selp?'sel':'',onclick:()=>{selp=p.id;R.analyzer()}},...[p.id,p.sip,p.dip,p.proto,p.sport||'–',p.dport||'–',p.size+' B'].map(x=>h('td',{},String(x))),h('td',{class:p.status=='delivered'?'ok':p.status=='dropped'?'bad':''},p.status)))))));
 const p=st.pk.find(x=>x.id==selp);if(!p)return v.append(h('p',{class:'m'},rows.length?'Select a packet to inspect it.':'No packets yet. Send one from the Simulation Console.'));
 const f=p.hops[0]||{},arp=p.proto=='ARP';
 v.append(h('div',{class:'cols',style:'margin-top:14px'},kv('Ethernet II (first hop)',[['Destination MAC',f.dm||'–'],['Source MAC',f.sm||'–'],['EtherType',arp?'0x0806 (ARP)':'0x0800 (IPv4)'],['Note','MAC addresses are rewritten at every routed hop; see Path']]),
  arp?kv('ARP',[['Opcode',p.flags],['Sender IP',p.sip],['Target IP',p.dip]]):kv('IPv4 header',[['Version / header length','4 / 20 bytes'],['TTL (initial → at end)',p.ttl0+' → '+p.ttl],['Protocol',{ICMP:'1 (ICMP)',TCP:'6 (TCP)',UDP:'17 (UDP)'}[p.tr]],['Source',p.sip],['Destination',p.dip],['Total length',p.size-14+' bytes']]),
  !arp&&p.tr=='ICMP'?kv('ICMP',[['Type',p.info.includes('request')?'8 (Echo request)':'0 (Echo reply)'],['Code',0]]):null,
  p.tr=='TCP'||p.tr=='UDP'?kv(p.tr,[['Source port',p.sport],['Destination port',p.dport],p.tr=='TCP'?['Flags',p.flags||'–']:['Length',p.size-34+' bytes']]):null,
  kv('Payload / summary',[['Info',p.info]]),
  kv('Path & result',[['Path',p.path.map(nm).join(' → ')],['Per-hop frames',p.hops.map(x=>`${x.a}→${x.b}: ${x.sm} → ${x.dm}`).join(' | ')||'–'],['Latency',p.lat+' ms (simulated)'],['Status',p.status+(p.why?' – '+p.why:'')]])))};
function pathHL(ids){return[...ids,...ids.slice(1).map((x,i)=>linkOf(ids[i],x)?.id).filter(Boolean)]}
R.routing=()=>{const v=view(),all=N.devs.filter(d=>d.type!='switch'),every=N.devs.map(d=>[d.id,d.name]),sv=S('svg',{});if(!dev(RT.d))RT.d=(all[1]||all[0]).id;if(!dev(RT.a))RT.a=C.src||all[0].id;if(!dev(RT.b))RT.b=C.dst||all[all.length-1].id;
 const d=dev(RT.d),ip=h('input',{placeholder:'destination IP, e.g. 10.0.1.10',value:RT.ip||''}),rows=routesOf(d).sort((x,y)=>parseCidr(y.net).l-parseCidr(x.net).l);
 const tp=(k,list)=>{const s=h('select',{},...list.map(([x,l])=>h('option',{value:x},l)));s.value=RT[k];s.onchange=()=>{RT[k]=s.value;R.routing()};return s};
 let res='',hl=[];const A=dev(RT.a),B=dev(RT.b);
 if(A&&B&&A!=B){const dj=dijkstra(A.id,B.id),t=A.type!='switch'&&B.type!='switch'?runQuiet(A,B,'ping'):null;
  res=h('div',{},h('p',{},h('b',{},'Shortest cable path (Dijkstra): '),dj?dj.map(x=>dev(x).name).join(' → ')+` (cost ${pathCost(dj)} ms)`:h('span',{class:'bad'},'No path: the devices are not connected.')),
   t&&t.pk[0]?h('p',{},h('b',{},'Routed path (hop-by-hop forwarding): '),t.pk[0].path.map(x=>dev(x).name).join(' → '),' ',h('b',{class:t.pk[0].status=='delivered'?'ok':'bad'},t.pk[0].status=='delivered'?'reachable':'FAILED: '+t.pk[0].why)):'');
  if(t&&t.pk[0])hl=pathHL(t.pk[0].path);else if(dj)hl=pathHL(dj)}
 v.append(h('div',{class:'split'},h('div',{class:'card'},h('h3',{},'Routing table'),h('div',{class:'bar'},tp('d',all.map(x=>[x.id,x.name])),h('button',{onclick:()=>{sel={id:d.id,k:'d'};go('config')}},'Edit routes')),
  h('table',{},h('thead',{},h('tr',{},...['Type','Network','Next hop','Interface'].map(x=>h('th',{},x)))),h('tbody',{},...rows.map(r=>h('tr',{},h('td',{},r.kind),h('td',{},r.net),h('td',{},r.via||'direct'),h('td',{},(lookup(d,r.via||n2ip(parseCidr(r.net).n))||{}).ifi!=null?d.ifaces[lookup(d,r.via||n2ip(parseCidr(r.net).n)).ifi].name:'–'))))),
  h('h3',{},'Longest-prefix lookup'),h('div',{class:'bar'},ip,h('button',{onclick:()=>{RT.ip=ip.value;R.routing()}},'Look up')),
  RT.ip?(ip2n(RT.ip)==null?h('p',{class:'bad'},'Enter a valid IPv4 address.'):(L=>L?(L.err?h('p',{class:'bad'},L.err):h('p',{},`Best match ${L.r.net} (/${L.c.l}, ${L.r.kind}) → next hop ${L.nh} via ${d.ifaces[L.ifi].name}`)):h('p',{class:'bad'},'No valid route: no routing entry matches '+RT.ip))(lookup(d,RT.ip))):''),
  h('div',{class:'card'},h('h3',{},'Path finder'),h('div',{class:'bar'},tp('a',every),'→',tp('b',every)),res,h('h3',{},'Cables'),toggles(R.routing))),h('div',{class:'card'},sv));drawTopo(sv,false,hl);
 v.lastChild.remove();v.append(h('div',{class:'card'},sv));};
R.monitor=()=>{const v=view(),s=st,tot=s.deliv+s.drop,up=N.links.filter(l=>l.up).length;
 const cd=(t,n)=>h('div',{class:'card'},h('h3',{},t),h('span',{class:'n'},n));
 v.append(h('div',{class:'grid'},cd('Packets sent',s.sent),cd('Delivered',s.deliv),cd('Packet loss',tot?pct(s.drop,tot):'n/a'),cd('Avg latency (sim.)',s.lat.length?avg(s.lat).toFixed(1)+' ms':'n/a'),cd('Throughput (sim.)',s.clk?(s.bytes*8/s.clk).toFixed(1)+' kbit/s':'n/a'),cd('Active connections',up+' / '+N.links.length)),
  h('p',{class:'m'},'All values come from the simulation clock, which advances by each cable’s configured latency. They are not real network measurements.'),
  h('div',{class:'row'},h('div',{class:'card'},h('h3',{},'Latency per delivered packet (ms)'),line(520,180,[{d:s.lat,c:'#38bdf8'}])),h('div',{class:'card'},h('h3',{},'Packets by protocol'),bars(520,180,Object.entries(s.proto)))),
  h('div',{class:'row'},h('div',{class:'card'},h('h3',{},'Device availability'),h('table',{},h('thead',{},h('tr',{},...['Device','Status','Cables up','Packets received'].map(x=>h('th',{},x)))),h('tbody',{},...N.devs.map(d=>{const ls=N.links.filter(l=>l.a==d.id||l.b==d.id),u=ls.filter(l=>l.up).length;return h('tr',{},h('td',{},d.name),h('td',{class:u?'ok':'bad'},u?'Reachable':ls.length?'Isolated (all cables down)':'Not cabled'),h('td',{},u+' / '+ls.length),h('td',{},s.dev[d.id]||0))})))),h('div',{class:'card'},h('h3',{},'Network event log'),logList(s.log.slice(-40).reverse()))))};
const byName=n=>N.devs.find(d=>d.name==n);
const CH=[{t:'Incorrect IP configuration',d:'PC1 cannot ping the web server. Find what is wrong with its addressing.',hint:'Compare PC1’s IP with its default gateway (192.168.1.1). Are they on the same subnet?',f:()=>{byName('PC1').ifaces[0].ip='192.168.2.10'},k:'ping'},
 {t:'Missing routing table entry',d:'R1 has no idea how to reach the server network. Ping PC1 → web server fails.',hint:'Add a static route on R1 for 10.0.1.0/24 via the firewall’s R1-facing address, 10.0.0.2.',f:()=>{byName('R1').routes=[]},k:'ping'},
 {t:'Firewall blocks TCP 443',d:'A TCP handshake from PC1 to the server on port 443 is refused.',hint:'Open FW1’s rules and remove the deny rule for tcp 443.',f:()=>{byName('FW1').fw.unshift({a:'deny',pr:'tcp',port:'443'})},k:'tcp',port:443},
 {t:'Disconnected link',d:'A cable is down somewhere between the firewall and the server.',hint:'In Network Studio, select the red dashed cable and reconnect it.',f:()=>{linkOf(byName('FW1').id,byName('SW2').id).up=false},k:'ping'},
 {t:'TTL expiration',d:'Packets from PC1 die on the way. Count the routers between PC1 and the server.',hint:'PC1’s initial TTL is far too small. Raise it (64 is typical).',f:()=>{byName('PC1').ttl=2},k:'ping'}];
function loadCh(i){if(!LAB.act)LAB.bk=JSON.stringify(N);sample();CH[i].f();LAB.act=i+1;sel=null;resetSim();go('studio')}
R.lab=()=>{const v=view(),m=h('div',{id:'labmsg',style:'margin-top:8px'});
 v.append(LAB.act?h('div',{class:'note'},`Challenge ${LAB.act} is loaded in Network Studio. Fix the network, then press Check. `,h('button',{onclick:()=>{N=JSON.parse(LAB.bk);LAB.act=0;sel=null;resetSim();R.lab()}},'Restore my project')):h('p',{class:'m'},'Each challenge replaces the topology with a broken copy of the sample network. Your own project is saved and can be restored.'),
  h('div',{class:'grid'},...CH.map((c,i)=>{const o=h('div',{class:'m'});return h('div',{class:'card'},h('h3',{},`Challenge ${i+1}: ${c.t}`),h('p',{},c.d),h('div',{class:'bar'},h('button',{class:'pri',onclick:()=>loadCh(i)},'Load'),h('button',{onclick:()=>{o.textContent='Hint: '+c.hint}},'Hint'),h('button',{onclick:()=>{if(LAB.act!=i+1){m.className='bad';m.textContent='Load challenge '+(i+1)+' first.';return}const r=runQuiet(byName('PC1'),byName('WebServer'),c.k,c.port);m.className=r.bad?'bad':'ok';m.textContent=r.bad?`✗ Not solved yet. Packet #${r.bad.id} (${r.bad.info}): ${r.bad.why||r.err}`:`✓ Solved. The packets were delivered end to end.`}},'Check')),o)})),m)};
const DOC=[['Quick start','Open Network Studio, drag devices, press Cable and click two devices to connect them. In the Simulation Console choose a source, destination and protocol, then press Send test packet. Use Pause, Resume and Step to control the event queue.'],
 ['How a packet is forwarded','1. The sender looks up a route (longest prefix wins) and checks the next hop is on a connected subnet. 2. The next hop must exist. 3. Dijkstra finds a working cable path through switches. 4. Routers and firewalls decrement TTL and drop at zero. 5. Firewall rules are evaluated. 6. The next hop is chosen again. 7. The packet is delivered or dropped with a reason.'],
 ['Protocols','ICMP ping, TCP three-way handshake, UDP, ARP, DNS and HTTP are scripted exchanges. Every packet is routed independently, so each reply is a real second trip and can fail separately.'],
 ['Analyzer and monitor','Every simulated packet is recorded with its Ethernet, IP and transport fields, path and result. The monitor derives loss, latency and throughput from the simulation clock, which advances by the latency of each cable.'],
 ['Limitations','Routing is static. The firewall is stateless. A device’s first configured IP is its primary address for scenarios. ARP results are not cached. Packets are simulated: nothing is captured from or sent to a real network.']];
R.docs=()=>view().append(h('div',{class:'cols'},...DOC.map(([t,x])=>h('div',{class:'card'},h('h3',{},t),h('p',{},x)))));
R.settings=()=>{const v=view(),sp=h('select',{},...[['1100','Slow'],['700','Normal'],['250','Fast']].map(([x,l])=>h('option',{value:x},l))),an=h('input',{type:'checkbox',style:'width:auto'});sp.value=String(cfg.speed);an.checked=cfg.anim;
 sp.onchange=()=>{cfg.speed=+sp.value;if(timer){pause();run()}};an.onchange=()=>cfg.anim=an.checked;
 v.append(h('div',{class:'cols'},h('div',{class:'card'},h('h3',{},'Simulation'),h('label',{class:'f'},'Step speed',sp),h('label',{class:'f'},'Animate packets ',an),h('button',{onclick:()=>{resetSim();msg('Statistics cleared')}},'Clear statistics and queue')),
  h('div',{class:'card'},h('h3',{},'Project (saved in this browser)'),h('div',{class:'bar'},h('button',{onclick:()=>{try{localStorage.setItem('packetflow.project',JSON.stringify(N));msg('Project saved')}catch(e){msg('Could not save: '+e.message)}}},'Save project'),
   h('button',{onclick:()=>{try{const j=JSON.parse(localStorage.getItem('packetflow.project'));if(!j)throw Error('no saved project');N=j;LAB.act=0;sel=null;resetSim();msg('Project loaded')}catch(e){msg('Could not load: '+e.message)}}},'Load project'),
   h('button',{onclick:()=>{if(confirm('Replace the topology with the sample network?')){sample();LAB.act=0;sel=null;touch();resetSim();msg('Sample network restored')}}},'Reset to sample'),
   h('button',{onclick:()=>{const a=h('a',{href:URL.createObjectURL(new Blob([JSON.stringify(N,null,1)])),download:'packetflow-project.json'});a.click()}},'Export JSON')),h('span',{id:'msg',class:'m'}))))};
if(typeof document!='undefined'){
 try{N=JSON.parse(localStorage.getItem('packetflow.project'));if(!N||!N.devs)throw 0}catch(e){sample()}
 sim=new Sim(st);sim.onHop=anim;
 PG.forEach(([id,l])=>$('#nav').append(h('a',{href:'#'+id,id:'n-'+id},l)));
 $('#qs').onclick=()=>{if(!LAB.act&&!dev(C.src))fixC();queue()};
 addEventListener('hashchange',render);render()}