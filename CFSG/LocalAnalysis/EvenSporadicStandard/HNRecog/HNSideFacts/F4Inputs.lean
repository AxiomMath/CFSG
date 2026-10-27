module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Data
public import CFSG.Sporadic.HNOddCore.QCheckInputs
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import CFSG.Sporadic.HNOddCore.ChainUtil
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Data
public meta import CFSG.Sporadic.HNOddCore.QCheckInputs
public meta import CFSG.Sporadic.HNOddCore.SCheckInputs
public meta import CFSG.Sporadic.HNOddCore.ChainUtil

public section

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native

@[expose] def qWordsJ : Array (List Int) := QData.qFlat.set! 3 q3Word

@[expose] def s800 : Array (Array Nat) := InvData.s4Perms

@[expose] def s12 : Array (Array Nat) := natArrs InvData.c4Nat

@[expose] def subProd12 (V : Array (Array Nat)) (m : Nat) : Array Nat :=
  (List.range V.size).foldl (fun acc i => if m.testBit i then pcomp 12 acc V[i]! else acc) (pid 12)

@[expose] def pathEval (K Ki : Array (Array Nat)) (w : List Int) (x : Nat) : Nat :=
  w.foldl (fun x l => (pletter K Ki l)[x]!) x

@[noinline, expose] def sideF4QOK : Bool :=
  let Si := pinvs 800 s800
  decide (qWordsJ.size = 8) && decide (InvData.qPerms.size = 8) && decide (s800.size = 11) &&
    allBelowN 8 fun i =>
      plettersOK 10 qWordsJ[i]! && peq 800 (pword 800 s800 Si qWordsJ[i]!) InvData.qPerms[i]!

@[expose] def evArr : Array (Array Nat) := eWords.map (pword 12 s12 (pinvs 12 s12))

@[expose] def bvArr : Array Nat := pword 12 s12 (pinvs 12 s12) bWord

@[noinline, expose] def sideF4PlusOK : Bool :=
  let Si := pinvs 800 s800
  let Si12 := pinvs 12 s12
  let B := qbList 800 InvData.qPerms
  decide (s12.size = 9) && decide (eWords.size = 5) && decide (eMasks.size = 5) &&
    (allBelowN 9 fun h => pisInv 12 s12[h]! Si12[h]!) &&
    (allBelowN 5 fun i => plettersOK 9 eWords[i]! && decide (eMasks[i]! < 256) &&
      peq 800 (pword 800 s800 Si eWords[i]!) B[eMasks[i]!]!) &&
    plettersOK 9 bWord && decide (bMask < 256) &&
    peq 800 (pword 800 s800 Si bWord) B[bMask]! &&
    (allBelowN 5 fun i => allBelowN 5 fun j =>
      peq 12 (pcomp 12 evArr[i]! evArr[j]!) (pcomp 12 evArr[j]! evArr[i]!)) &&
    (allBelowN 5 fun i => peq 12 (pcomp 12 evArr[i]! evArr[i]!) (pid 12)) &&
    (allBelowN 32 fun a => allBelowN 32 fun b =>
      decide (b ≤ a) || !(peq 12 (subProd12 evArr a) (subProd12 evArr b))) &&
    !(peq 12 (pcomp 12 evArr[3]! bvArr) (pcomp 12 bvArr evArr[3]!))

@[noinline, expose] def sideF4ClassOK : Bool :=
  let Ki := pinvs 256 colPerms
  decide (labTab.size = 256) && decide (toWords.size = 256) && decide (fromWords.size = 256) &&
    decide (repTab.size = 4) && decide (colPerms.size = 11) &&
    (allBelowN 256 fun m =>
      decide (labTab[m]! < 4) && plettersOK 10 toWords[m]! && plettersOK 10 fromWords[m]! &&
        pathEval colPerms Ki toWords[m]! m == repTab[labTab[m]!]! &&
        pathEval colPerms Ki fromWords[m]! repTab[labTab[m]!]! == m) &&
    (allBelowN 16 fun b =>
      let cnt := ((List.range 256).filter fun m => b.testBit labTab[m]!).length
      decide (256 % cnt ≠ 0) || cnt == 1 || cnt == 256)

@[expose] def inV (i m : Nat) : Bool := (subsData[i]!).contains m

@[noinline, expose] def sideF4FamOK : Bool :=
  decide (subsData.size = 10) && decide (sigArrs.size = 10) &&
    (allBelowN 10 fun s => allBelowN 10 fun i => allBelowN 256 fun m =>
      inV ((sigArrs[s]!)[i]!) m == inV i ((colPerms[s]!)[m]!)) &&
    (allBelowN 10 fun i => allBelowN 10 fun j =>
      decide (j ≤ i) || (List.range 256).any fun m => inV i m != inV j m) &&
    (allBelowN 10 fun s => pisInv 10 sigArrs[s]! (pinvCand 10 sigArrs[s]!)) &&
    chainCheck 10 sigArrs sigWords sigBase sigSizes

end CFSG.EvenSporadicStandard.HNRecog.SideF4
