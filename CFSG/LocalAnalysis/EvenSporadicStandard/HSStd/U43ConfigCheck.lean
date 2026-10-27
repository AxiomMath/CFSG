module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
public import CFSG.Sporadic.SmallOddCore.CentData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
public meta import CFSG.Sporadic.SmallOddCore.CentData
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
  CFSG.EvenSporadicStandard.M24Std.CU43

@[expose] def closureCap : ℕ := 50000

@[expose] def permInvOK (x : Table) : Bool :=
  permOK 820 x && CFSG.Sporadic.Th.Native.invOK 820 x (invT 820 x)

@[expose] def memCos (ks : List ℕ) (x : Table) : Bool :=
  ks.any fun k => decide (k < 8) && inP (compA 820 (natArr x) (invCand 820 (tArr k)))

@[expose] def enumOK (A : Array Table) (cap size : ℕ) : Bool :=
  A.all permInvOK &&
    mulTreeOK 820 A (mulClosureH 820 A cap).1 (mulClosureH 820 A cap).2.1
      (mulClosureH 820 A cap).2.2 &&
    closedOK 820 (A ++ A.map (invT 820)) (mulClosureH 820 A cap).1 &&
    hkeysDistinct 820 (mulClosureH 820 A cap).1.toList && (mulClosureH 820 A cap).1.size == size

@[expose] def classOK (gG : Array Table) (x : Table) (cap sizeG csz : ℕ) : Bool :=
  gG.all permInvOK &&
    conjTreeOK 820 gG (gG.map (invT 820)) x (conjClosureH 820 gG (gG.map (invT 820)) x cap).1
      (conjClosureH 820 gG (gG.map (invT 820)) x cap).2.1
      (conjClosureH 820 gG (gG.map (invT 820)) x cap).2.2 &&
    hkeysDistinct 820 (conjClosureH 820 gG (gG.map (invT 820)) x cap).1.toList &&
    decide (sizeG ≤ csz * (conjClosureH 820 gG (gG.map (invT 820)) x cap).1.size)

@[expose] def coverOK (cg : Array Table) (y0 : Table) (cap : ℕ) : Bool :=
  conjTreeOK 820 cg (cg.map (invT 820)) y0 (conjClosureH 820 cg (cg.map (invT 820)) y0 cap).1
    (conjClosureH 820 cg (cg.map (invT 820)) y0 cap).2.1
    (conjClosureH 820 cg (cg.map (invT 820)) y0 cap).2.2 &&
  (mulClosureH 820 cg cap).1.all fun x =>
    !ordTest 820 3 x || memT 820 (conjClosureH 820 cg (cg.map (invT 820)) y0 cap).1 x

@[expose] def cpOf (Tt c : Table) : Table := conjT 820 Tt Tt c

@[expose] def relFree (y c c' : Table) : Bool :=
  (List.range 3).all fun a => (List.range 3).all fun b => (List.range 3).all fun d =>
    (a == 0 && b == 0 && d == 0) ||
      !tblEq 820 (compT 820 (compT 820 (powT 820 a y) (powT 820 b c)) (powT 820 d c')) (idT 820)

@[expose] def candOK (Tt y0 c : Table) : Bool :=
  ordTest 820 3 c && commTT 820 c (cpOf Tt c) && commTT 820 y0 (cpOf Tt c) &&
    relFree y0 c (cpOf Tt c)

@[expose] def kOK (Tt c k : Table) : Bool :=
  involOK 820 k && commTT 820 k (cpOf Tt c) && commTT 820 k (cpOf Tt k) &&
    tblEq 820 (compT 820 (conjT 820 k k c) c) (idT 820)

structure CaseData where
  ks : List ℕ
  sizeG : ℕ
  gensG : Array Table
  Tt : Table
  cg : Array Table
  y0 : Table
  yg : Array Table
  ysz : ℕ
  nsol : ℕ

@[expose] def yEnum (d : CaseData) : Array Table := (mulClosureH 820 d.yg closureCap).1

@[expose] def solList (d : CaseData) : List (Table × Table) :=
  ((yEnum d).toList.filter (candOK d.Tt d.y0)).flatMap fun c =>
    ((yEnum d).toList.filter (kOK d.Tt c)).map fun k => (c, k)

@[expose] def cent5Of (d : CaseData) (s : Table × Table) : ℕ :=
  ((yEnum d).toList.filter fun z => commTT 820 z s.1 && commTT 820 z (cpOf d.Tt s.1) &&
    commTT 820 z s.2 && commTT 820 z (cpOf d.Tt s.2)).length

@[expose] def caseCheck (d : CaseData) : Bool :=
  permOK 820 d.Tt && permOK 820 d.y0 &&
    d.gensG.all (memCos d.ks) &&
    classOK d.gensG d.Tt closureCap d.sizeG 2880 &&
    d.cg.all (fun g => memCos d.ks g && commTT 820 g d.Tt) &&
    enumOK d.cg closureCap 2880 && coverOK d.cg d.y0 closureCap &&
    d.yg.all (fun g => memCos d.ks g && commTT 820 g d.y0) &&
    enumOK d.yg closureCap d.ysz && classOK d.gensG d.y0 closureCap d.sizeG d.ysz &&
    (solList d).length == d.nsol && (solList d).all fun s => cent5Of d s == 3

end CFSG.EvenSporadicStandard.HSStd.U43
