import { useState, useEffect, useRef, useCallback } from "react";

// ═══════════════════════════════════════════════════════════════
// 31-EDO Constants
// ═══════════════════════════════════════════════════════════════
const CH_MAPS = [
  [0,2,5,8,10,13,15,18,20,23,26,28],
  [1,3,6,9,11,14,16,19,21,24,27,29],
  [-1,1,4,7,9,12,14,17,19,22,25,27],
];
const KEY_TYPE = [
  'mw','uw','lb','ub','lw','mw','uw','lb','ub','lw',
  'mw','uw','lw','mw','uw','lb','ub','lw',
  'mw','uw','lb','ub','lw','mw','uw','lb','ub','lw',
  'mw','uw','lw',
];
const PIANO_LO = [
  {wk:0},{wk:0},{bk:1},{bk:1},{wk:1},{wk:1},{wk:1},
  {bk:2},{bk:2},{wk:2},{wk:2},{wk:2},
  {wk:3},{wk:3},{wk:3},{bk:4},{bk:4},{wk:4},{wk:4},{wk:4},
  {bk:5},{bk:5},{wk:5},{wk:5},{wk:5},{bk:6},{bk:6},
  {wk:6},{wk:6},{wk:6},{wk:7},
];
const DFLT_COLORS = [
  '#e74c3c','#3498db','#2ecc71','#f39c12',
  '#9b59b6','#1abc9c','#e67e22','#ff6b9d',
  '#00bcd4','#8bc34a','#ff5722','#607d8b',
];
const HAS_LBK = [false,true,true,false,true,true,true];
const HAS_RBK = [true,true,false,true,true,true,false];
const hasLBk = c => c > 0  && HAS_LBK[(5+c)%7];
const hasRBk = c => c < 51 && HAS_RBK[(5+c)%7];

// ═══════════════════════════════════════════════════════════════
// MIDI Parser
// ═══════════════════════════════════════════════════════════════
function parseMidi(buf) {
  const d = new Uint8Array(buf); let p = 0;
  const u32=()=>{const v=((d[p]<<24)|(d[p+1]<<16)|(d[p+2]<<8)|d[p+3])>>>0;p+=4;return v;};
  const u16=()=>{const v=(d[p]<<8)|d[p+1];p+=2;return v;};
  const tag=()=>String.fromCharCode(d[p],d[p+1],d[p+2],d[p+3]);
  const vlq=()=>{let v=0,b;do{b=d[p++];v=(v<<7)|(b&0x7f);}while(b&0x80);return v;};
  if(tag()!=='MThd')throw new Error('Not a MIDI file');
  p+=4;u32();
  const fmt=u16(),ntrk=u16(),div=u16(),tracks=[];
  for(let t=0;t<ntrk;t++){
    if(tag()!=='MTrk'){p+=4;const sl=u32();p+=sl;continue;}
    p+=4;const len=u32(),end=p+len,evs=[];let tick=0,rs=0;
    while(p<end){
      tick+=vlq();let st=d[p];
      if(st&0x80){p++;if(st<0xF0)rs=st;}else{st=rs;}
      const et=st>>4,ch=(st&0xf)+1;
      if(et===0x9){const n=d[p++],v=d[p++];evs.push(v?{t:'on',tick,ch,n,v}:{t:'off',tick,ch,n});}
      else if(et===0x8){const n=d[p++];p++;evs.push({t:'off',tick,ch,n});}
      else if(et===0xa||et===0xb||et===0xe){p+=2;}
      else if(et===0xc||et===0xd){p+=1;}
      else if(st===0xff){const mt=d[p++],ml=vlq();
        if(mt===0x51&&ml>=3)evs.push({t:'tempo',tick,tempo:(d[p]<<16)|(d[p+1]<<8)|d[p+2]});
        else if(mt===0x58&&ml>=4)evs.push({t:'ts',tick,num:d[p],den:1<<d[p+1]});
        p+=ml;}
      else if(st===0xf0||st===0xf7){p+=vlq();}
      else p++;
    }
    p=end;tracks.push(evs);
  }
  return{fmt,div,tracks};
}

// ═══════════════════════════════════════════════════════════════
// Note & Tempo Builder
// ═══════════════════════════════════════════════════════════════
function buildNotes(midi){
  const{div,tracks}=midi;
  const tempos=[{tick:0,tempo:500000,time:0}],timeSigs=[{tick:0,num:4,den:4,time:0}];
  tracks.forEach(tr=>tr.forEach(e=>{if(e.t==='tempo')tempos.push(e);if(e.t==='ts')timeSigs.push(e);}));
  tempos.sort((a,b)=>a.tick-b.tick);
  for(let i=1;i<tempos.length;i++){const p=tempos[i-1];tempos[i].time=p.time+(tempos[i].tick-p.tick)/div*p.tempo/1e6;}
  const t2s=tick=>{let i=tempos.length-1;while(i>0&&tempos[i].tick>tick)i--;const{tick:t0,tempo:tp,time:t}=tempos[i];return t+(tick-t0)/div*tp/1e6;};
  timeSigs.sort((a,b)=>a.tick-b.tick);timeSigs.forEach(ts=>{ts.time=t2s(ts.tick);});
  const notes=[];let maxTime=0,trackCount=0;
  tracks.forEach(tr=>{
    if(!tr.filter(e=>(e.t==='on'||e.t==='off')&&e.ch>=1&&e.ch<=3).length)return;
    const tIdx=trackCount++;const active=new Map();
    tr.forEach(e=>{
      if(e.ch<1||e.ch>3)return;
      const key=`${e.ch}_${e.n}`;
      if(e.t==='on'){active.set(key,e);}
      else if(e.t==='off'){const on=active.get(key);if(on){
        const m=CH_MAPS[e.ch-1],idx=((e.n-60)%12+12)%12,oct=Math.floor((e.n-60)/12);
        const edoPos=m[idx]+oct*31,st=t2s(on.tick),et=t2s(e.tick);
        if(et>maxTime)maxTime=et;notes.push({tIdx,ch:e.ch,note:e.n,vel:on.v,st,et,edoPos});active.delete(key);}}
    });
    active.forEach(on=>{const m=CH_MAPS[on.ch-1],idx=((on.n-60)%12+12)%12,oct=Math.floor((on.n-60)/12);
      notes.push({tIdx,ch:on.ch,note:on.n,vel:on.v,st:t2s(on.tick),et:Math.max(maxTime,1),edoPos:m[idx]+oct*31});});
  });
  return{notes,tempos,timeSigs,duration:maxTime,trackCount};
}

// ═══════════════════════════════════════════════════════════════
// Keyboard Map
// ═══════════════════════════════════════════════════════════════
function buildKbMap(){
  const edoToKb=new Map(),colTypeToEdo=new Map(),gapTypeToEdo=new Map();
  for(let n=21;n<=108;n++)for(let ci=0;ci<3;ci++){
    const m=CH_MAPS[ci],idx=((n-60)%12+12)%12,oct=Math.floor((n-60)/12);
    const edoPos=m[idx]+oct*31;if(edoToKb.has(edoPos))continue;
    const edo31Oct=Math.floor(edoPos/31),posInOct=((edoPos%31)+31)%31;
    const lay=PIANO_LO[posInOct],cCol=23+edo31Oct*7;
    if(lay.wk!=null){const col=cCol+lay.wk;if(col>=0&&col<=51){
      const kb={isBlack:false,col,type:KEY_TYPE[posInOct]};edoToKb.set(edoPos,kb);
      const k=`${col}_${kb.type}`;if(!colTypeToEdo.has(k))colTypeToEdo.set(k,edoPos);
    }}else{const gapCol=cCol+lay.bk;const kb={isBlack:true,gapCol,type:KEY_TYPE[posInOct]};
      edoToKb.set(edoPos,kb);const k=`${gapCol}_${kb.type}`;if(!gapTypeToEdo.has(k))gapTypeToEdo.set(k,edoPos);}
  }
  return{edoToKb,colTypeToEdo,gapTypeToEdo};
}

// ═══════════════════════════════════════════════════════════════
// Drawing Helpers
// ═══════════════════════════════════════════════════════════════
function ptUW(x0,x1,h1,bkH,ov,hL,hR){const ny=h1-ov,pts=[[x0,0],[x1,0]];if(hR)pts.push([x1,ny],[x1-bkH,ny],[x1-bkH,h1]);else pts.push([x1,h1]);if(hL)pts.push([x0+bkH,h1],[x0+bkH,ny],[x0,ny]);else pts.push([x0,h1]);return pts;}
function ptMW(x0,x1,h1,h2,bkH,hL,hR){if(hL&&hR)return[[x0+bkH,h1],[x1-bkH,h1],[x1-bkH,h2],[x0+bkH,h2]];if(hL)return[[x0+bkH,h1],[x1,h1],[x1,h2],[x0+bkH,h2]];if(hR)return[[x0,h1],[x1-bkH,h1],[x1-bkH,h2],[x0,h2]];return[[x0,h1],[x1,h1],[x1,h2],[x0,h2]];}
function ptLW(x0,x1,h2,H,bkH,ov,hL,hR){const ny=h2+ov,pts=[];if(hL)pts.push([x0+bkH,h2],[x0+bkH,ny],[x0,ny]);else pts.push([x0,h2]);pts.push([x0,H],[x1,H]);if(hR)pts.push([x1,ny],[x1-bkH,ny],[x1-bkH,h2]);else pts.push([x1,h2]);return pts;}
function applyPath(ctx,pts,fill,stroke){if(!pts||pts.length<2)return;ctx.beginPath();ctx.moveTo(pts[0][0],pts[0][1]);for(let i=1;i<pts.length;i++)ctx.lineTo(pts[i][0],pts[i][1]);ctx.closePath();if(fill)ctx.fill();if(stroke)ctx.stroke();}
function roundRect(ctx,x,y,w,h,r,fill=true,stroke=false){if(r<=0){if(fill)ctx.fillRect(x,y,w,h);if(stroke){ctx.beginPath();ctx.rect(x,y,w,h);ctx.stroke();}return;}const rr=Math.min(r,w/2,h/2);ctx.beginPath();ctx.moveTo(x+rr,y);ctx.lineTo(x+w-rr,y);ctx.arcTo(x+w,y,x+w,y+rr,rr);ctx.lineTo(x+w,y+h-rr);ctx.arcTo(x+w,y+h,x+w-rr,y+h,rr);ctx.lineTo(x+rr,y+h);ctx.arcTo(x,y+h,x,y+h-rr,rr);ctx.lineTo(x,y+rr);ctx.arcTo(x,y,x+rr,y,rr);ctx.closePath();if(fill)ctx.fill();if(stroke)ctx.stroke();}
function hexToRgb(h){const s=h.replace('#','');const n=parseInt(s.length===3?s.split('').map(c=>c+c).join(''):s,16);return[(n>>16)&255,(n>>8)&255,n&255];}
function lighten(h,a){const[r,g,b]=hexToRgb(h);return`rgb(${Math.min(255,r+a*255|0)},${Math.min(255,g+a*255|0)},${Math.min(255,b+a*255|0)})`;}
function darken(h,a){const[r,g,b]=hexToRgb(h);return`rgb(${Math.max(0,r-a*255|0)},${Math.max(0,g-a*255|0)},${Math.max(0,b-a*255|0)})`;}
function fmtTime(s){const m=Math.floor(s/60),ss=(s%60).toFixed(2).padStart(5,'0');return`${m}:${ss}`;}

// ═══════════════════════════════════════════════════════════════
// Draw Piano Roll
// ═══════════════════════════════════════════════════════════════
function drawPianoRoll(canvas,notes,now,eMin,eMax,hZoom,trackColors,bgColor,cornerRad,
                       activeBrighter,showKeyboard,tempos,timeSigs,showTempo,
                       phColor,phOpacity,bgImageEl,bgImgOpacity,tempoColor){
  const ctx=canvas.getContext('2d');
  const CW=canvas.width,CH=canvas.height,numRows=eMax-eMin+1;
  if(numRows<=0||CW<=0||CH<=0)return;
  const rowH=CH/numRows,playX=CW/2;
  ctx.fillStyle=bgColor;ctx.fillRect(0,0,CW,CH);
  if(bgImageEl&&bgImageEl.complete&&bgImgOpacity>0){
    ctx.save();ctx.globalAlpha=bgImgOpacity/100;ctx.drawImage(bgImageEl,0,0,CW,CH);ctx.restore();
  }
  ctx.save();
  notes.forEach(note=>{
    if(note.edoPos<eMin||note.edoPos>eMax)return;
    const x0=playX+(note.st-now)*hZoom,x1=playX+(note.et-now)*hZoom;
    if(x1<0||x0>CW)return;
    const isActive=note.st<=now&&now<=note.et;
    const tsinceOn=now-note.st;
    const scaleY=(tsinceOn>=0&&tsinceOn<0.1)?1+0.35*(1-tsinceOn/0.1):1;
    const baseColor=(trackColors&&trackColors[note.tIdx])||DFLT_COLORS[note.tIdx%DFLT_COLORS.length];
    const fill=isActive?(activeBrighter?lighten(baseColor,0.35):darken(baseColor,0.3)):baseColor;
    const ry=rowH*(eMax-note.edoPos),noteH=rowH*scaleY,ny=ry-(noteH-rowH)/2;
    const nx=Math.max(0,x0),nw=Math.min(CW,x1)-nx;if(nw<=0)return;
    ctx.globalAlpha=1;ctx.fillStyle=fill;roundRect(ctx,nx,ny,nw,noteH,Math.min(cornerRad,rowH/2));
    if(isActive){ctx.globalAlpha=0.45;ctx.strokeStyle=fill;ctx.lineWidth=1.5;roundRect(ctx,nx,ny,nw,noteH,Math.min(cornerRad,rowH/2),false,true);}
  });
  ctx.globalAlpha=1;ctx.restore();
  const[pr,pg,pb]=hexToRgb(phColor||'#ffffff');
  ctx.save();ctx.strokeStyle=`rgba(${pr},${pg},${pb},${(phOpacity??70)/100})`;ctx.lineWidth=2;
  ctx.beginPath();ctx.moveTo(playX,0);ctx.lineTo(playX,CH);ctx.stroke();ctx.restore();
  if(showTempo&&tempos&&tempos.length){
    let ti=0;while(ti<tempos.length-1&&tempos[ti+1].time<=now)ti++;
    const bpm=Math.round(60e6/tempos[ti].tempo);
    let si=0;if(timeSigs){while(si<timeSigs.length-1&&timeSigs[si+1].time<=now)si++;}
    const ts=timeSigs?timeSigs[si]:null;
    ctx.save();ctx.font='bold 62px monospace';ctx.fillStyle=tempoColor||'rgba(255,255,255,0.5)';
    ctx.fillText(ts?`${bpm} BPM  ${ts.num}/${ts.den}`:`${bpm} BPM`,12,70);ctx.restore();
  }
  if(showKeyboard){
    const kbH=Math.round(CH/6);
    const grad=ctx.createLinearGradient(0,CH-kbH-24,0,CH-kbH);
    grad.addColorStop(0,'rgba(0,0,0,0)');grad.addColorStop(1,'rgba(0,0,0,0.32)');
    ctx.fillStyle=grad;ctx.fillRect(0,CH-kbH-24,CW,24);
  }
}

// ═══════════════════════════════════════════════════════════════
// Draw Keyboard
// ═══════════════════════════════════════════════════════════════
function drawKeyboard(canvas,kbData,activeSet,colForEdo,flashMap,showFlash){
  const{colTypeToEdo,gapTypeToEdo}=kbData;
  const ctx=canvas.getContext('2d');const CW=canvas.width,CH=canvas.height;
  if(CW<=0||CH<=0)return;
  const kbH=Math.round(CH/6),offY=CH-kbH,kw=CW/52,bkH=kw*0.3,bkW=kw*0.6;
  const h1=kbH/3,h2=2*kbH/3,ov=kbH/6;
  ctx.save();ctx.translate(0,offY);ctx.fillStyle='#0a0a0a';ctx.fillRect(0,0,CW,kbH);
  const kf=(ep,def)=>activeSet.has(ep)?colForEdo.get(ep)||def:def;
  for(let col=0;col<52;col++){
    const x=col*kw,x1=x+kw,hL=hasLBk(col),hR=hasRBk(col);
    ctx.fillStyle=kf(colTypeToEdo.get(`${col}_uw`),'#eeeeee');applyPath(ctx,ptUW(x,x1,h1,bkH,ov,hL,hR),true,false);
    ctx.fillStyle=kf(colTypeToEdo.get(`${col}_mw`),'#eeeeee');applyPath(ctx,ptMW(x,x1,h1,h2,bkH,hL,hR),true,false);
    ctx.fillStyle=kf(colTypeToEdo.get(`${col}_lw`),'#eeeeee');applyPath(ctx,ptLW(x,x1,h2,kbH,bkH,ov,hL,hR),true,false);
  }
  const drawn=new Set();
  for(let g=1;g<=51;g++){const ux=g*kw;['ub','lb'].forEach(type=>{
    const key=`${g}_${type}`,edoPos=gapTypeToEdo.get(key);if(edoPos===undefined)return;
    drawn.add(key);ctx.fillStyle=kf(edoPos,'#333333');ctx.fillRect(ux-bkH,type==='ub'?h1-ov:h2-ov,bkW,ov*2);
  });}
  if(showFlash&&flashMap.size>0){flashMap.forEach((op,ep)=>{
    const kb=kbData.edoToKb.get(ep);if(!kb)return;
    ctx.fillStyle=`rgba(255,255,255,${op*0.85})`;
    if(kb.isBlack){ctx.fillRect(kb.gapCol*kw-bkH,kb.type==='ub'?h1-ov:h2-ov,bkW,ov*2);}
    else{const x=kb.col*kw,hL=hasLBk(kb.col),hR=hasRBk(kb.col);
      applyPath(ctx,kb.type==='uw'?ptUW(x,x+kw,h1,bkH,ov,hL,hR):kb.type==='mw'?ptMW(x,x+kw,h1,h2,bkH,hL,hR):ptLW(x,x+kw,h2,kbH,bkH,ov,hL,hR),true,false);}
  });}
  ctx.strokeStyle='#000000';ctx.lineWidth=1;
  for(let col=0;col<52;col++){const x=col*kw,x1=x+kw,hL=hasLBk(col),hR=hasRBk(col);
    applyPath(ctx,ptUW(x,x1,h1,bkH,ov,hL,hR),false,true);
    applyPath(ctx,ptMW(x,x1,h1,h2,bkH,hL,hR),false,true);
    applyPath(ctx,ptLW(x,x1,h2,kbH,bkH,ov,hL,hR),false,true);}
  drawn.forEach(key=>{const[g,type]=key.split('_');ctx.strokeRect(+g*kw-bkH,type==='ub'?h1-ov:h2-ov,bkW,ov*2);});
  ctx.restore();
}

const KB_DATA=buildKbMap();
const ENC=new TextEncoder();
const TERMS_URL='./Terms.html'; // ← 利用規約URLをここに設定

// ═══════════════════════════════════════════════════════════════
// Main App
// ═══════════════════════════════════════════════════════════════
export default function App(){
  // Data
  const[midiName,  setMidiName  ]=useState('');
  const[audioName, setAudioName ]=useState('');
  const[noteData,  setNoteData  ]=useState(null);
  const[trackCount,setTrackCount]=useState(0);
  const[midiDuration,setMidiDuration]=useState(0);
  const[loadErr,   setLoadErr   ]=useState('');

  // Playback
  const[isPlaying, setIsPlaying ]=useState(false);
  const[currentTime,setCurrentTime]=useState(0);
  const[audioOffset,setAudioOffset]=useState(0);

  // Visual settings
  const[trackColors,setTrackColors]=useState({});
  const[vZoom,    setVZoom    ]=useState(80);
  const[scrollY,  setScrollY  ]=useState(0);
  const[hZoom,    setHZoom    ]=useState(200);
  const[bgColor,  setBgColor  ]=useState('#0d0d0f');
  const[bgImage,  setBgImage  ]=useState(null);
  const[bgImgOpacity,setBgImgOpacity]=useState(80);
  const[cornerRad,setCornerRad]=useState(3);
  const[activeBrighter,setActiveBrighter]=useState(true);
  const[showKb,   setShowKb   ]=useState(true);
  const[showFlash,setShowFlash]=useState(true);
  const[showTempo,setShowTempo]=useState(true);
  const[tempoColor,setTempoColor]=useState('#ffffff');
  const[phColor,  setPhColor  ]=useState('#ffffff');
  const[phOpacity,setPhOpacity]=useState(70);
  const[settingsOpen,setSettingsOpen]=useState(false);

  // Export
  const[exportPhase,setExportPhase]=useState('idle'); // idle|selecting|exporting|done|error
  const[exportProgress,setExportProgress]=useState(0);
  const[exportLabel,setExportLabel]=useState('');

  // Refs
  const canvasRef     =useRef(null);
  const audioCtxRef   =useRef(null);
  const audioSrcRef   =useRef(null);
  const audioBufferRef=useRef(null);
  const audioRawRef   =useRef(null);   // Uint8Array of original audio file
  const audioExtRef   =useRef('mp3');  // 'mp3' or 'wav'
  const audioOffsetRef=useRef(0);      // mirror of audioOffset state for callbacks
  const rafRef        =useRef(null);
  const playStateRef  =useRef({playing:false,ctxStart:0,songStart:0});
  const currentTimeRef=useRef(0);
  const midiDurRef    =useRef(0);
  const flashMapRef   =useRef(new Map());
  const prevActiveRef =useRef(new Set());
  const noteDataRef   =useRef(null);
  const bgImageElRef  =useRef(null);
  const midiNameRef   =useRef('');

  const settingsRef=useRef({
    trackColors:{},vZoom:80,scrollY:0,hZoom:200,bgColor:'#0d0d0f',
    bgImageEl:null,bgImgOpacity:80,cornerRad:3,activeBrighter:true,
    showKb:true,showFlash:true,showTempo:true,tempoColor:'#ffffff',
    phColor:'#ffffff',phOpacity:70,edoRange:{min:-62,max:62},
  });

  useEffect(()=>{noteDataRef.current=noteData;},[noteData]);
  useEffect(()=>{audioOffsetRef.current=audioOffset;},[audioOffset]);
  useEffect(()=>{midiNameRef.current=midiName;},[midiName]);

  useEffect(()=>{
    settingsRef.current={
      trackColors,vZoom,scrollY,hZoom,bgColor,
      bgImageEl:bgImageElRef.current,bgImgOpacity,cornerRad,activeBrighter,
      showKb,showFlash,showTempo,tempoColor,phColor,phOpacity,
      edoRange:settingsRef.current.edoRange,
    };
  },[trackColors,vZoom,scrollY,hZoom,bgColor,bgImgOpacity,cornerRad,
     activeBrighter,showKb,showFlash,showTempo,tempoColor,phColor,phOpacity]);

  // Canvas resize (16:9)
  useEffect(()=>{
    const canvas=canvasRef.current;if(!canvas)return;
    const sync=()=>{const r=canvas.getBoundingClientRect();const w=Math.round(r.width),h=Math.round(r.height);
      if(w>0&&h>0){if(canvas.width!==w)canvas.width=w;if(canvas.height!==h)canvas.height=h;}};
    const ro=new ResizeObserver(sync);ro.observe(canvas);sync();return()=>ro.disconnect();
  },[]);

  // RAF loop
  useEffect(()=>{
    const canvas=canvasRef.current;if(!canvas)return;
    const loop=()=>{
      try{
        const ps=playStateRef.current;
        if(ps.playing&&audioCtxRef.current){
          const newTime=ps.songStart+(audioCtxRef.current.currentTime-ps.ctxStart);
          const dur=midiDurRef.current;
          if(dur>0&&newTime>=dur){
            if(audioSrcRef.current){try{audioSrcRef.current.stop();}catch(_){}audioSrcRef.current=null;}
            currentTimeRef.current=dur;playStateRef.current.playing=false;
            setCurrentTime(dur);setIsPlaying(false);
          }else{currentTimeRef.current=newTime;setCurrentTime(newTime);}
        }
        const nd=noteDataRef.current,s=settingsRef.current;
        if(!nd||canvas.width===0||canvas.height===0){rafRef.current=requestAnimationFrame(loop);return;}
        const now=currentTimeRef.current;
        const{vZoom,scrollY,edoRange,hZoom,bgColor,bgImageEl,bgImgOpacity,cornerRad,
              activeBrighter,showKb,showFlash,showTempo,tempoColor,phColor,phOpacity}=s;
        const centerEdo=Math.round((edoRange.min+edoRange.max)/2)+scrollY;
        const half=Math.ceil(vZoom/2),eMin=centerEdo-half,eMax=centerEdo+half;
        const activeSet=new Set(),colForEdo=new Map(),newActive=new Set();
        nd.notes.forEach(note=>{if(note.st<=now&&now<=note.et){
          activeSet.add(note.edoPos);
          colForEdo.set(note.edoPos,(s.trackColors&&s.trackColors[note.tIdx])||DFLT_COLORS[note.tIdx%DFLT_COLORS.length]);
          newActive.add(note.edoPos);}});
        newActive.forEach(ep=>{if(!prevActiveRef.current.has(ep))flashMapRef.current.set(ep,performance.now());});
        prevActiveRef.current=newActive;
        const flashMap=new Map(),toDelete=[];
        flashMapRef.current.forEach((ts,ep)=>{const age=(performance.now()-ts)/1000;
          if(age<0.05)flashMap.set(ep,1-age/0.05);else toDelete.push(ep);});
        toDelete.forEach(ep=>flashMapRef.current.delete(ep));
        drawPianoRoll(canvas,nd.notes,now,eMin,eMax,hZoom,s.trackColors,bgColor,cornerRad,activeBrighter,
          showKb,nd.tempos,nd.timeSigs,showTempo,phColor,phOpacity,bgImageEl,bgImgOpacity,tempoColor);
        if(showKb)drawKeyboard(canvas,KB_DATA,activeSet,colForEdo,flashMap,showFlash);
      }catch(err){console.error('[HyDiator]',err);}
      rafRef.current=requestAnimationFrame(loop);
    };
    rafRef.current=requestAnimationFrame(loop);return()=>cancelAnimationFrame(rafRef.current);
  },[]);

  // ── File handlers ──────────────────────────────────────────
  const handleMidi=useCallback(async file=>{
    setLoadErr('');
    try{
      const buf=await file.arrayBuffer(),midi=parseMidi(buf),nd=buildNotes(midi);
      setNoteData(nd);noteDataRef.current=nd;setTrackCount(nd.trackCount);
      const dur=nd.duration+4;setMidiDuration(dur);midiDurRef.current=dur;
      if(nd.notes.length){
        const mn=Math.min(...nd.notes.map(n=>n.edoPos)),mx=Math.max(...nd.notes.map(n=>n.edoPos));
        const pad=Math.max(5,Math.ceil((mx-mn)*0.1));
        settingsRef.current.edoRange={min:mn-pad,max:mx+pad};
        const nv=Math.max(20,Math.min(160,mx-mn+2*pad));
        settingsRef.current.vZoom=nv;settingsRef.current.scrollY=0;setScrollY(0);setVZoom(nv);
      }
      const cols={};for(let i=0;i<nd.trackCount;i++)cols[i]=DFLT_COLORS[i%DFLT_COLORS.length];
      setTrackColors(cols);settingsRef.current.trackColors=cols;
      setMidiName(file.name);midiNameRef.current=file.name;
      currentTimeRef.current=0;setCurrentTime(0);playStateRef.current={playing:false,ctxStart:0,songStart:0};
    }catch(e){setLoadErr(`MIDI error: ${e.message}`);console.error(e);}
  },[]);

  const handleAudio=useCallback(async file=>{
    setLoadErr('');
    try{
      if(!audioCtxRef.current)audioCtxRef.current=new AudioContext();
      const raw=await file.arrayBuffer();
      audioRawRef.current=new Uint8Array(raw.slice(0));
      audioExtRef.current=file.name.match(/\.(\w+)$/)?.[1]?.toLowerCase()||'mp3';
      const decoded=await audioCtxRef.current.decodeAudioData(raw.slice(0));
      audioBufferRef.current=decoded;setAudioName(file.name);
    }catch(e){setLoadErr(`Audio error: $ {e.message}`);}
  },[]);

  const handleBgImage=useCallback(file=>{
    if(!file)return;
    const url=URL.createObjectURL(file);const img=new Image();
    img.onload=()=>{bgImageElRef.current=img;setBgImage(url);settingsRef.current.bgImageEl=img;};
    img.src=url;
  },[]);

  const handleFiles=useCallback(files=>{
    Array.from(files).forEach(f=>{
      if(f.name.match(/\.(mid|midi)$/i))handleMidi(f);
      else if(f.name.match(/\.(mp3|wav)$/i))handleAudio(f);
      else if(f.name.match(/\.(png|jpe?g)$/i))handleBgImage(f);
    });
  },[handleMidi,handleAudio,handleBgImage]);

  // ── Transport ──────────────────────────────────────────────
  const stopAudio=useCallback(()=>{
    if(audioSrcRef.current){try{audioSrcRef.current.stop();}catch(_){}audioSrcRef.current=null;}
  },[]);

  const startAudio=useCallback(fromTime=>{
    if(!audioBufferRef.current||!audioCtxRef.current)return;
    stopAudio();
    const src=audioCtxRef.current.createBufferSource();
    src.buffer=audioBufferRef.current;src.connect(audioCtxRef.current.destination);
    const audioPos=fromTime+audioOffsetRef.current/1000;
    if(audioPos>=0){src.start(0,audioPos);}
    else{src.start(audioCtxRef.current.currentTime+(-audioPos),0);}
    audioSrcRef.current=src;
  },[stopAudio]);

  const play=useCallback(()=>{
    if(!noteData)return;
    if(audioCtxRef.current?.state==='suspended')audioCtxRef.current.resume();
    const t=currentTimeRef.current>=midiDurRef.current?0:currentTimeRef.current;
    if(t===0){currentTimeRef.current=0;setCurrentTime(0);}
    startAudio(t);
    playStateRef.current={playing:true,ctxStart:audioCtxRef.current?.currentTime||0,songStart:t};
    setIsPlaying(true);
  },[noteData,startAudio]);

  const pause=useCallback(()=>{stopAudio();playStateRef.current.playing=false;setIsPlaying(false);},[stopAudio]);

  const seek=useCallback(t=>{
    const clamped=Math.max(0,Math.min(t,midiDurRef.current||t));
    const was=playStateRef.current.playing;stopAudio();
    currentTimeRef.current=clamped;setCurrentTime(clamped);
    playStateRef.current={playing:false,ctxStart:0,songStart:clamped};
    if(was)setTimeout(()=>{if(!audioCtxRef.current)return;startAudio(clamped);
      playStateRef.current={playing:true,ctxStart:audioCtxRef.current.currentTime,songStart:clamped};setIsPlaying(true);},30);
  },[stopAudio,startAudio]);

  // ── MP4 Export (WebCodecs H.264 + ffmpeg AAC mux) ──────────
  const doExport=useCallback(async(fps)=>{
    const nd=noteDataRef.current;if(!nd)return;
    setExportPhase('exporting');setExportProgress(0);setExportLabel('Initializing…');

    try{
      // ── WebCodecs support check ───────────────────────────────
      if(!('VideoEncoder' in window))throw new Error('WebCodecs not supported in this browser');

      const W=1920,H=1080;
      const CODEC='avc1.640028'; // H.264 High Profile @ Level 4.0

      const support=await VideoEncoder.isConfigSupported({
        codec:CODEC,width:W,height:H,bitrate:10_000_000,framerate:fps,
      });
      if(!support.supported)throw new Error('H.264 HW encoding not supported in this browser');

      // ── mp4-muxer setup ───────────────────────────────────────
      const{Muxer,ArrayBufferTarget}=await import('mp4-muxer');
      const target=new ArrayBufferTarget();
      const muxer=new Muxer({
        target,
        video:{codec:'avc',width:W,height:H},
        fastStart:'in-memory',
      });

      // ── VideoEncoder setup ────────────────────────────────────
      let encError=null;
      const encoder=new VideoEncoder({
        output:(chunk,meta)=>muxer.addVideoChunk(chunk,meta),
        error:(e)=>{encError=e;},
      });
      encoder.configure({
        codec:CODEC,width:W,height:H,
        bitrate:10_000_000,framerate:fps,
        hardwareAcceleration:'prefer-hardware',
      });

      // ── Render + encode all frames ────────────────────────────
      const offCanvas=document.createElement('canvas');offCanvas.width=W;offCanvas.height=H;
      const s={...settingsRef.current};
      const dur=midiDurRef.current;
      const totalFrames=Math.ceil(dur*fps);
      const US=1_000_000/fps; // microseconds per frame

      const centerEdo=Math.round((s.edoRange.min+s.edoRange.max)/2)+s.scrollY;
      const half=Math.ceil(s.vZoom/2);
      const eMin=centerEdo-half,eMax=centerEdo+half;

      setExportLabel('Encoding video…');
      for(let fi=0;fi<totalFrames;fi++){
        if(encError)throw encError;

        // Backpressure: yield if encoder queue is deep
        while(encoder.encodeQueueSize>20)
          await new Promise(r=>setTimeout(r,5));

        const t=fi/fps;
        const activeSet=new Set(),colForEdo=new Map();
        nd.notes.forEach(note=>{if(note.st<=t&&t<=note.et){
          activeSet.add(note.edoPos);
          colForEdo.set(note.edoPos,(s.trackColors&&s.trackColors[note.tIdx])||DFLT_COLORS[note.tIdx%DFLT_COLORS.length]);}});
        const flashMap=new Map();
        if(s.showFlash)nd.notes.forEach(note=>{const age=t-note.st;
          if(age>=0&&age<0.05)flashMap.set(note.edoPos,Math.max(flashMap.get(note.edoPos)||0,1-age/0.05));});

        drawPianoRoll(offCanvas,nd.notes,t,eMin,eMax,s.hZoom,s.trackColors,s.bgColor,s.cornerRad,
          s.activeBrighter,s.showKb,nd.tempos,nd.timeSigs,s.showTempo,s.phColor,s.phOpacity,
          s.bgImageEl,s.bgImgOpacity,s.tempoColor);
        if(s.showKb)drawKeyboard(offCanvas,KB_DATA,activeSet,colForEdo,flashMap,s.showFlash);

        const frame=new VideoFrame(offCanvas,{timestamp:fi*US,duration:US});
        encoder.encode(frame,{keyFrame:fi%(Math.ceil(fps)*2)===0});
        frame.close();

        setExportProgress(Math.round((fi+1)/totalFrames*60));
      }

      setExportLabel('Flushing encoder…');
      await encoder.flush();
      encoder.close();
      muxer.finalize();
      const videoBuffer=target.buffer; // H.264 in MP4 container (video only)
      setExportProgress(65);

      // ── ffmpeg: AAC encode + mux ──────────────────────────────
      const{createFFmpeg}=await import('@ffmpeg/ffmpeg');
      const ff=createFFmpeg({corePath:'/ffmpeg/ffmpeg-core.js',log:false});
      setExportLabel('Loading ffmpeg (audio)…');
      await ff.load();
      setExportProgress(70);

      ff.FS('writeFile','video.mp4',new Uint8Array(videoBuffer));

      if(audioRawRef.current){
        const ext=audioExtRef.current;
        ff.FS('writeFile',`audio.${ext}`,audioRawRef.current);
        const offSec=audioOffsetRef.current/1000;
        const audioInput=offSec>=0
          ?['-ss',String(offSec),'-i',`audio.${ext}`]
          :['-itsoffset',String(-offSec),'-i',`audio.${ext}`];

        setExportLabel('Encoding audio (AAC)…');
        ff.setProgress(({ratio})=>setExportProgress(Math.round(70+(ratio||0)*26)));
        await ff.run(
          '-i','video.mp4',...audioInput,
          '-c:v','copy','-c:a','aac','-b:a','512k',
          '-shortest','-movflags','+faststart','output.mp4'
        );
      }else{
        ff.setProgress(({ratio})=>setExportProgress(Math.round(70+(ratio||0)*26)));
        await ff.run('-i','video.mp4','-c','copy','-movflags','+faststart','output.mp4');
      }

      setExportProgress(97);setExportLabel('Downloading…');

      const data=ff.FS('readFile','output.mp4');
      const url=URL.createObjectURL(new Blob([data.buffer],{type:'video/mp4'}));
      const a=document.createElement('a');
      a.href=url;a.download=(midiNameRef.current.replace(/\.(mid|midi)$/i,'')||'output')+'.mp4';
      document.body.appendChild(a);a.click();document.body.removeChild(a);URL.revokeObjectURL(url);

      setExportProgress(100);setExportPhase('done');setTimeout(()=>setExportPhase('idle'),2500);

    }catch(err){
      console.error('Export error:',err);
      setExportLabel(`Failed: $ {(err?.message||String(err)).slice(0,80)}`);
      setExportPhase('error');setTimeout(()=>setExportPhase('idle'),6000);
    }
  },[]);

  const onDrop=useCallback(e=>{e.preventDefault();handleFiles(e.dataTransfer.files);},[handleFiles]);
  const onDragOver=useCallback(e=>e.preventDefault(),[]);

  // ═══════════════════════════════════════════════════════════
  // Render
  // ═══════════════════════════════════════════════════════════
  const canExport=!!noteData;

  return(
    <div style={{display:'flex',flexDirection:'column',height:'100vh',
                 background:'#080810',color:'#e0e0e0',
                 fontFamily:'"Times New Roman",monospace,serif',overflow:'hidden'}}>

      {/* Top Bar */}
      <div style={{display:'flex',alignItems:'center',gap:12,padding:'8px 14px',
                   background:'#0e0e18',borderBottom:'1px solid #222',flexShrink:0,flexWrap:'wrap'}}>
        <span style={{color:'#7c6aff',fontWeight:700,fontSize:15,letterSpacing:1,marginRight:4}}>HyDiator</span>
        <FileBtn label="MIDI"  name={midiName}  accept=".mid,.midi" color="#7c6aff" onChange={e=>handleFiles(e.target.files)}/>
        <FileBtn label="Audio" name={audioName} accept=".mp3,.wav"  color="#3dcfb0" onChange={e=>handleFiles(e.target.files)}/>
        {loadErr&&<span style={{color:'#e74c3c',fontSize:12}}>{loadErr}</span>}
        <div style={{marginLeft:'auto',display:'flex',alignItems:'center',gap:8}}>
          <label style={{fontSize:11,color:'#888'}}>Offset (ms)</label>
          <input type="number" value={audioOffset} onChange={e=>setAudioOffset(+e.target.value)}
            style={{width:82,background:'#1a1a2a',border:'1px solid #333',color:'#ccc',padding:'3px 6px',borderRadius:4,fontSize:12}}/>
          <button onClick={()=>setSettingsOpen(o=>!o)}
            style={{background:settingsOpen?'#7c6aff':'#1a1a2a',border:'1px solid #333',
                    color:'#ccc',padding:'4px 10px',borderRadius:4,cursor:'pointer',fontSize:12}}>
            ⚙ Settings
          </button>
        </div>
      </div>

      {/* Main area */}
      <div style={{display:'flex',flex:1,overflow:'hidden'}}>
        {/* Canvas */}
        <div style={{flex:1,background:'#000',overflow:'hidden',display:'flex',
                     flexDirection:'column',justifyContent:'flex-start'}}
             onDrop={onDrop} onDragOver={onDragOver}>
          <div style={{position:'relative',width:'100%'}}>
            <canvas ref={canvasRef} style={{display:'block',width:'100%',aspectRatio:'16/9'}}/>
            {!noteData&&(
              <div style={{position:'absolute',inset:0,display:'flex',alignItems:'center',
                           justifyContent:'center',pointerEvents:'none'}}>
                <div style={{border:'2px dashed #333',borderRadius:12,padding:'40px 60px',
                             textAlign:'center',background:'rgba(0,0,0,0.65)'}}>
                  <div style={{fontSize:36,marginBottom:12}}>HyDiator</div>
                  <div style={{color:'#7c6aff',fontWeight:700,fontSize:16,marginBottom:8}}>31-EDO MIDI Visualizer</div>
                  <div style={{color:'#555',fontSize:13}}>Drop a <b style={{color:'#888'}}>.mid</b> and <b style={{color:'#888'}}>.mp3/.wav</b> file here</div>
                  <div style={{color:'#444',fontSize:11,marginTop:8}}>or use the buttons above</div>
                </div>
              </div>
            )}
          </div>
        </div>

        {/* Settings Panel */}
        {settingsOpen&&(
          <div style={{width:320,background:'#0e0e18',borderLeft:'1px solid #1e1e2e',overflowY:'auto',padding:14,flexShrink:0}}>
            <Section title="Display">
              <Row label="H Zoom (px/s)"><Slider min={30} max={800} value={hZoom} onChange={v=>{setHZoom(v);settingsRef.current.hZoom=v;}}/><Val>{hZoom}</Val></Row>
              <Row label="V Zoom (rows)"><Slider min={10} max={400} value={vZoom} onChange={v=>{setVZoom(v);settingsRef.current.vZoom=v;}}/><Val>{vZoom}</Val></Row>
              <Row label="V Scroll"><Slider min={-100} max={100} value={scrollY} onChange={v=>{setScrollY(v);settingsRef.current.scrollY=v;}}/><Val>{scrollY}</Val></Row>
              <Row label="Corner radius"><Slider min={0} max={8} value={cornerRad} onChange={v=>{setCornerRad(v);settingsRef.current.cornerRad=v;}}/><Val>{cornerRad}px</Val></Row>
              <Row label="BG color">
                <input type="color" value={bgColor} onChange={e=>{setBgColor(e.target.value);settingsRef.current.bgColor=e.target.value;}} style={{width:32,height:22,border:'none',background:'none',cursor:'pointer'}}/>
                <span style={{fontSize:11,color:'#777'}}>{bgColor}</span>
              </Row>
              <Row label="Playhead color">
                <input type="color" value={phColor} onChange={e=>{setPhColor(e.target.value);settingsRef.current.phColor=e.target.value;}} style={{width:32,height:22,border:'none',background:'none',cursor:'pointer'}}/>
                <span style={{fontSize:11,color:'#777'}}>{phColor}</span>
              </Row>
              <Row label="Playhead opacity"><Slider min={0} max={100} value={phOpacity} onChange={v=>{setPhOpacity(v);settingsRef.current.phOpacity=v;}}/><Val>{phOpacity}%</Val></Row>
            </Section>

            <Section title="Background Image">
              <Row label="Image (PNG/JPG)">
                <label style={{cursor:'pointer',display:'flex',alignItems:'center',gap:6}}>
                  <span style={{background:'#1a1a2a',border:'1px solid #444',color:'#aaa',padding:'2px 8px',borderRadius:4,fontSize:11}}>{bgImage?'Change…':'Load…'}</span>
                  <input type="file" accept=".png,.jpg,.jpeg" onChange={e=>e.target.files[0]&&handleBgImage(e.target.files[0])} style={{display:'none'}}/>
                  {bgImage&&<button onClick={()=>{setBgImage(null);bgImageElRef.current=null;settingsRef.current.bgImageEl=null;}} style={{background:'none',border:'none',color:'#e74c3c',cursor:'pointer',fontSize:11}}>✕</button>}
                </label>
              </Row>
              <Row label="Opacity"><Slider min={0} max={100} value={bgImgOpacity} onChange={v=>{setBgImgOpacity(v);settingsRef.current.bgImgOpacity=v;}}/><Val>{bgImgOpacity}%</Val></Row>
            </Section>

            <Section title="Notes">
              <Row label="Active notes"><Toggle value={activeBrighter} labels={['Darker','Brighter']} onChange={v=>{setActiveBrighter(v);settingsRef.current.activeBrighter=v;}}/></Row>
            </Section>

            <Section title="Keyboard">
              <Row label="Show keyboard"><Toggle value={showKb} labels={['Off','On']} onChange={v=>{setShowKb(v);settingsRef.current.showKb=v;}}/></Row>
              <Row label="Onset flash"><Toggle value={showFlash} labels={['Off','On']} onChange={v=>{setShowFlash(v);settingsRef.current.showFlash=v;}}/></Row>
            </Section>

            <Section title="Overlay">
              <Row label="Tempo / time sig"><Toggle value={showTempo} labels={['Off','On']} onChange={v=>{setShowTempo(v);settingsRef.current.showTempo=v;}}/></Row>
              <Row label="Overlay color">
                <input type="color" value={tempoColor} onChange={e=>{setTempoColor(e.target.value);settingsRef.current.tempoColor=e.target.value;}} style={{width:32,height:22,border:'none',background:'none',cursor:'pointer'}}/>
                <span style={{fontSize:11,color:'#777'}}>{tempoColor}</span>
              </Row>
            </Section>

            {trackCount>0&&(
              <Section title="Track Colors">
                {Array.from({length:trackCount},(_,i)=>(
                  <Row key={i} label={`Track ${i+1}`}>
                    <input type="color" value={trackColors[i]||DFLT_COLORS[i%DFLT_COLORS.length]}
                      onChange={e=>{const nc={...trackColors,[i]:e.target.value};setTrackColors(nc);settingsRef.current.trackColors=nc;}}
                      style={{width:32,height:22,border:'none',background:'none',cursor:'pointer'}}/>
                    <span style={{fontSize:11,color:'#777'}}>{trackColors[i]||DFLT_COLORS[i%DFLT_COLORS.length]}</span>
                  </Row>
                ))}
              </Section>
            )}

            {/* Terms of Use */}
            <div style={{marginTop:8,paddingTop:12,borderTop:'1px solid #1e1e2e'}}>
              <a href={TERMS_URL} target="_blank" rel="noopener noreferrer"
                 style={{display:'flex',alignItems:'center',justifyContent:'center',gap:6,
                         fontSize:12,color:'#7c6aff',textDecoration:'none',
                         padding:'6px 10px',borderRadius:5,border:'1px solid #7c6aff44',
                         background:'#7c6aff11',cursor:'pointer'}}>
                Terms of Use <span style={{fontSize:10,opacity:0.7}}>↗</span>
              </a>
            </div>
          </div>
        )}
      </div>

      {/* Transport Bar */}
      <div style={{background:'#0a0a14',borderTop:'1px solid #1e1e2e',padding:'8px 14px',flexShrink:0}}>
        <div style={{display:'flex',alignItems:'center',gap:10}}>
          <span style={{fontSize:13,color:'#7c6aff',minWidth:72,fontVariantNumeric:'tabular-nums'}}>{fmtTime(currentTime)}</span>
          <button onClick={isPlaying?pause:play} disabled={!noteData}
            style={{background:isPlaying?'#7c6aff':'#1a1a2a',border:'1px solid #333',color:'#fff',
                    padding:'5px 16px',borderRadius:6,cursor:noteData?'pointer':'not-allowed',fontSize:16}}>
            {isPlaying?'⏸':'▶'}
          </button>
          <input type="range" min={0} max={midiDuration||1} step={0.01}
            value={Math.min(currentTime,midiDuration||currentTime)}
            onChange={e=>seek(+e.target.value)}
            style={{flex:1,accentColor:'#7c6aff',cursor:'pointer'}}/>
          <span style={{fontSize:13,color:'#555',minWidth:72,textAlign:'right',fontVariantNumeric:'tabular-nums'}}>{fmtTime(midiDuration)}</span>

          {/* Export area */}
          <div style={{position:'relative',marginLeft:8,flexShrink:0}}>

            {/* FPS popup */}
            {exportPhase==='selecting'&&(
              <div style={{position:'absolute',bottom:'calc(100% + 6px)',right:0,
                           background:'#1a1a2a',border:'1px solid #444',borderRadius:8,
                           padding:'10px 12px',display:'flex',alignItems:'center',gap:8,
                           whiteSpace:'nowrap',boxShadow:'0 4px 16px rgba(0,0,0,0.5)',zIndex:10}}>
                <span style={{fontSize:12,color:'#999'}}>Frame rate:</span>
                {[30,60].map(fps=>(
                  <button key={fps} onClick={()=>doExport(fps)}
                    style={{background:'#7c6aff',border:'none',color:'#fff',
                            padding:'5px 14px',borderRadius:5,cursor:'pointer',fontSize:13,fontWeight:700}}>
                    {fps} fps
                  </button>
                ))}
                <button onClick={()=>setExportPhase('idle')}
                  style={{background:'none',border:'none',color:'#666',cursor:'pointer',fontSize:16,lineHeight:1}}>✕</button>
              </div>
            )}

            {/* Idle: Export button */}
            {(exportPhase==='idle')&&(
              <button onClick={()=>canExport&&setExportPhase('selecting')}
                disabled={!canExport}
                style={{background:canExport?'#1a1a2a':'#111',border:`1px solid ${canExport?'#555':'#333'}`,
                        color:canExport?'#ccc':'#444',padding:'5px 12px',borderRadius:6,
                        cursor:canExport?'pointer':'not-allowed',fontSize:12,minWidth:110}}>
                Export MP4
              </button>
            )}

            {/* Exporting: progress bar */}
            {(exportPhase==='exporting'||exportPhase==='done'||exportPhase==='error')&&(
              <div style={{minWidth:200,background:'#111',border:'1px solid #333',borderRadius:6,
                           padding:'5px 10px',display:'flex',flexDirection:'column',gap:3}}>
                <div style={{display:'flex',justifyContent:'space-between',alignItems:'center'}}>
                  <span style={{fontSize:11,color:exportPhase==='error'?'#e74c3c':exportPhase==='done'?'#2ecc71':'#aaa',
                                maxWidth:160,overflow:'hidden',textOverflow:'ellipsis',whiteSpace:'nowrap'}}>
                    {exportPhase==='done'?'✓ Done!':exportPhase==='error'?exportLabel:exportLabel}
                  </span>
                  <span style={{fontSize:11,color:'#7c6aff',fontWeight:700}}>{exportProgress}%</span>
                </div>
                <div style={{background:'#222',borderRadius:3,height:6,overflow:'hidden'}}>
                  <div style={{height:'100%',borderRadius:3,transition:'width 0.3s ease',
                               background:exportPhase==='error'?'#e74c3c':exportPhase==='done'?'#2ecc71':'#7c6aff',
                               width:`${exportProgress}%`}}/>
                </div>
              </div>
            )}
          </div>
        </div>

        <div style={{display:'flex',gap:16,marginTop:4,fontSize:11,color:'#444'}}>
          {midiName&&<span>MIDI: <span style={{color:'#666'}}>{midiName}</span></span>}
          {audioName&&<span>Audio: <span style={{color:'#666'}}>{audioName}</span></span>}
          {noteData&&(()=>{
            const ch1=noteData.notes.filter(n=>n.ch===1).length;
            const ch2=noteData.notes.filter(n=>n.ch===2).length;
            const ch3=noteData.notes.filter(n=>n.ch===3).length;
            return<span style={{color:'#555'}}>{noteData.notes.length} notes · {trackCount} track{trackCount!==1?'s':''} ·{' '}
              <span style={{color:'#7c6aff'}}>Ch1:{ch1}</span>{' '}
              <span style={{color:'#3dcfb0'}}>Ch2:{ch2}</span>{' '}
              <span style={{color:'#f39c12'}}>Ch3:{ch3}</span>
            </span>;
          })()}
          {noteData&&!audioBufferRef.current&&(
            <span style={{color:'#e67e22'}}>⚠ Load an audio file to enable playback</span>
          )}
        </div>
      </div>
    </div>
  );
}

// ─── UI helpers ───────────────────────────────────────────────
function FileBtn({label,name,accept,onChange,color}){
  return(<label style={{display:'flex',alignItems:'center',gap:6,cursor:'pointer'}}>
    <span style={{background:'#1a1a2a',border:`1px solid ${color}44`,color,padding:'3px 10px',borderRadius:4,fontSize:12,fontWeight:700,userSelect:'none'}}>{label}</span>
    {name?<span style={{fontSize:11,color:'#666',maxWidth:140,overflow:'hidden',textOverflow:'ellipsis',whiteSpace:'nowrap'}}>{name}</span>
         :<span style={{fontSize:11,color:'#444'}}>no file</span>}
    <input type="file" accept={accept} onChange={onChange} style={{display:'none'}}/>
  </label>);}

function Section({title,children}){
  return(<div style={{marginBottom:16}}>
    <div style={{fontSize:10,color:'#555',letterSpacing:2,textTransform:'uppercase',marginBottom:8,borderBottom:'1px solid #1e1e2e',paddingBottom:4}}>{title}</div>
    {children}
  </div>);}

function Row({label,children}){
  return(<div style={{display:'flex',alignItems:'center',gap:8,marginBottom:7}}>
    <span style={{fontSize:11,color:'#777',width:104,flexShrink:0}}>{label}</span>
    <div style={{display:'flex',alignItems:'center',gap:6,flex:1,minWidth:0}}>{children}</div>
  </div>);}

function Slider({min,max,value,onChange}){
  return<input type="range" min={min} max={max} value={value} onChange={e=>onChange(+e.target.value)} style={{flex:1,accentColor:'#7c6aff',cursor:'pointer',minWidth:0}}/>;}

function Val({children}){
  return<span style={{fontSize:11,color:'#888',minWidth:40,textAlign:'right',flexShrink:0}}>{children}</span>;}

function Toggle({value,onChange,labels}){
  return(<button onClick={()=>onChange(!value)}
    style={{background:value?'#7c6aff22':'#1a1a2a',border:`1px solid ${value?'#7c6aff':'#333'}`,
            color:value?'#7c6aff':'#666',padding:'2px 10px',borderRadius:4,cursor:'pointer',fontSize:11}}>
    {value?labels[1]:labels[0]}
  </button>);}