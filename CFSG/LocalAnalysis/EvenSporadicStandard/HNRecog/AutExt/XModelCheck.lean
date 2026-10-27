module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XModelData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvCheck

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[inline, expose] def commB (x y : Table) : Bool :=
  ap x (ap y 0) == ap y (ap x 0) && ap x (ap y 1) == ap y (ap x 1)

@[inline, expose] def commB3 (u m t : Table) : Bool :=
  ap u (ap m (ap t 0)) == ap t (ap u (ap m 0)) && ap u (ap m (ap t 1)) == ap t (ap u (ap m 1))

@[expose] def xBaseOK (Xl : Array Table) : Bool :=
  Xl.all fun x => ap x 0 != 0 || ap x 1 != 1 || tblEq 1408 x (idT 1408)

@[expose] def commTab (x xi y yi : Table) : Table :=
  compT 1408 (compT 1408 (compT 1408 x y) xi) yi

@[expose] def relAT (x xi y yi : Table) : Table :=
  let c := compT 1408
  c (c (c (c (c (c (c (c (c (c (c (c (c x x) y) xi) yi) x) y) xi) xi) y) xi) y) xi) yi

@[expose, noinline] def xF1OK (Nl F1l : Array Table) : Bool :=
  Nl.all fun y => !ordTest 1408 5 y || memT 1408 F1l y

@[expose, noinline] def xF2OK (Nl F2l : Array Table) (c1 c1i A : Table) : Bool :=
  Nl.all fun y =>
    !(order3OK 1408 y && tblEq 1408 (relAT c1 c1i y (compT 1408 y y)) A) || memT 1408 F2l y

@[expose] def xInnerOK (_ : Unit := ()) : Bool :=
  let A := tabW wordA
  let Z := tabW wordZ
  let u1 := tabW xU1
  let u2 := tabW xU2
  let u1i := invT 1408 u1
  let u2i := invT 1408 u2
  let P1 := tabW xP1
  let Q1 := tabW xQ1
  let P2 := tabW xP2
  let Q2 := tabW xQ2
  let C1 := tabW xC1
  let C2 := tabW xC2
  let P1i := invT 1408 P1
  let Q1i := invT 1408 Q1
  let P2i := invT 1408 P2
  let Q2i := invT 1408 Q2
  let c1i := powT 1408 4 C1
  let c2i := compT 1408 C2 C2
  let gX := #[u1, u2]
  let gXi := #[u1i, u2i]
  let D := #[tabW xD1, tabW xD2, tabW xD3, tabW xD4]
  let Di := D.map (invT 1408)
  let Nl := subgroupList invCap [xC1, xC2]
  let F1 := conjClosureH 1408 gX gXi C1 invCap
  let F2 := conjClosureH 1408 D Di C2 invCap
  gensOK &&
    [xU1, xU2, xP1, xQ1, xP2, xQ2, xC1, xC2, xD1, xD2, xD3, xD4, wordA, wordZ].all wordOK &&
    commTT 1408 A Z && commTT 1408 A u1 && commTT 1408 A u2 &&
    invOK 1408 u1 u1i && invOK 1408 u2 u2i &&
    commTT 1408 P1 Z && commTT 1408 Q1 Z && commTT 1408 P2 Z && commTT 1408 Q2 Z &&
    invOK 1408 P1 P1i && invOK 1408 Q1 Q1i && invOK 1408 P2 P2i && invOK 1408 Q2 Q2i &&
    tblEq 1408 C1 (commTab P1 P1i Q1 Q1i) && tblEq 1408 C2 (commTab P2 P2i Q2 Q2i) &&
    enumW invCap 7680 [xC1, xC2] &&
    memT 1408 Nl (commTab u1 u1i u2 u2i) &&
    memT 1408 Nl (conjT 1408 u1 u1i C1) && memT 1408 Nl (conjT 1408 u1 u1i C2) &&
    memT 1408 Nl (conjT 1408 u2 u2i C1) && memT 1408 Nl (conjT 1408 u2 u2i C2) &&
    memT 1408 Nl (conjT 1408 u1i u1 C1) && memT 1408 Nl (conjT 1408 u1i u1 C2) &&
    memT 1408 Nl (conjT 1408 u2i u2 C1) && memT 1408 Nl (conjT 1408 u2i u2 C2) &&
    ordTest 1408 5 C1 && order3OK 1408 C2 &&
    tblEq 1408 (relAT C1 c1i C2 c2i) A &&
    conjTreeOK 1408 gX gXi C1 F1.1 F1.2.1 F1.2.2 && xF1OK Nl F1.1 &&
    D.all (fun d => commTT 1408 d C1 && commTT 1408 d Z) &&
    D.all (fun d => invOK 1408 d (invT 1408 d)) &&
    conjTreeOK 1408 D Di C2 F2.1 F2.2.1 F2.2.2 && xF2OK Nl F2.1 C1 c1i A

@[expose] def goodCount (c : Nat) : Bool := c == 384 || c == 768

@[expose, noinline] def xCentTauOK (Xl Nl Zl : Array Table) (u1 u2 τ : Table) : Bool :=
  let CN := Nl.filter fun m => commB m τ
  Xl.all (fun g =>
      !CN.all (fun m => commB g m) || memT 1408 Zl g || memT 1408 Zl (compT 1408 g τ)) &&
    Nl.any (fun m => commB3 u1 m τ) && Nl.any (fun m => commB3 u2 m τ)

@[expose, noinline] def xCentLoopOK (Xl Nl Zl : Array Table) (u1 u2 : Table) : Bool :=
  Xl.all fun τ =>
    !invoOK 1408 τ || !goodCount (Xl.filter fun g => commB g τ).size ||
      xCentTauOK Xl Nl Zl u1 u2 τ

@[expose] def xCentOK (_ : Unit := ()) : Bool :=
  let C1 := tabW xC1
  let C2 := tabW xC2
  let Xl := subgroupList invCap classz.centGens
  let Nl := subgroupList invCap [xC1, xC2]
  let Zl := Nl.filter fun z => commB z C1 && commB z C2
  Xl.size == 30720 && xBaseOK Xl && xCentLoopOK Xl Nl Zl (tabW xU1) (tabW xU2)

end CFSG.EvenSporadicStandard.HNRecog.Section4.XModel
