module

public import CFSG.Sporadic.Schreier.J4SElevenData
public import Certificates.Data.CFSGNative.J4.FixScan

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4.Native

@[expose] def natV2 (n : Nat) : V2 := V2.ofFn fun j => n.testBit j

@[expose] def pairRows (P : Array Nat × Array Nat) : Array V2 := P.1.map natV2

@[expose] def fixBs : BFSState := bfs (frTable rowsA) (frTable rowsB) rootV nPts

@[expose] def qxFixPts : List V2 := [
  ⟨2464328887847859957, 50131164433373⟩,
  ⟨7827863139613149364, 253433280781276⟩,
  ⟨5880236960221509959, 210923785547233⟩,
  ⟨3142738623145933932, 103183868778333⟩,
  ⟨3759750707843926198, 161111427813687⟩,
  ⟨5787354417116314108, 92667643577224⟩,
  ⟨4202100500383845949, 244395051142495⟩,
  ⟨10139468673073992525, 74047358385071⟩,
  ⟨17291781965267035276, 92819172889734⟩,
  ⟨11599172497610491577, 228284667947765⟩,
  ⟨11743137680746247232, 222559833858366⟩]

@[expose] def storedOK (st : BFSState) (v : V2) : Bool :=
  decide (findIdx st.keys st.slots v - 1 < nPts) && (rdV2 st.keys (findIdx st.keys st.slots v - 1)).beq v

@[expose] def ptsOK (st : BFSState) (T : Array V2) (pts : List V2) : Bool :=
  decide pts.Nodup && pts.all fun v => v.wf && (frApply T v).beq v && storedOK st v

@[expose] def chkFixQ11 : Bool :=
  fixScanOK fixBs.keys nPts (frTable (pairRows CFSG.Sporadic.J4Schreier.QXn)) qxFixPts 3 &&
    fixScanOK fixBs.keys nPts (frTable (pairRows CFSG.Sporadic.J4Schreier.QZn)) [] 3 &&
    ptsOK fixBs (frTable (pairRows CFSG.Sporadic.J4Schreier.QXn)) qxFixPts

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
