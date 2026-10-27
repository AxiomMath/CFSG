module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Data
public import CFSG.GH74.M12.HypGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma4Data

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open CFSG.EvenSporadicStandard.Fin76b CFSG.GH74.M12 CFSG.GH74.M12.Hyp

@[expose] def wA1 : List (Fin 5 × Bool) := wA ++ wB
@[expose] def wA2 : List (Fin 5 × Bool) := wA ++ wA ++ wU ++ wR
@[expose] def wB1 : List (Fin 5 × Bool) := wA ++ invW wB
@[expose] def wB2 : List (Fin 5 × Bool) := invW wA ++ invW wB ++ wR
@[expose] def wT : List (Fin 5 × Bool) := wA ++ wA ++ wB ++ wU
@[expose] def wSP : List (Fin 5 × Bool) := sw [4, 3, 3, 4]

@[expose] def sActOK : Bool :=
  tblEq 14 (tblW (invW wSP ++ wA1 ++ wSP)) (tblW wA2) &&
  tblEq 14 (tblW (invW wSP ++ wA2 ++ wSP)) (tblW (wA1 ++ wA2)) &&
  tblEq 14 (tblW (invW wSP ++ wB1 ++ wSP)) (tblW wB2) &&
  tblEq 14 (tblW (invW wSP ++ wB2 ++ wSP)) (tblW (wB1 ++ wB2)) &&
  tblEq 14 (tblW (invW wSP ++ wE ++ wSP)) (tblW wE) &&
  tblEq 14 (tblW (wSP ++ wSP ++ wSP)) (idT 14) &&
  tblEq 14 (tblW (wSP ++ wT ++ wSP ++ wT)) (idT 14) &&
  tblEq 14 (tblW (wA1 ++ wA1)) (tblW wJ)

@[expose] def kWords : List (List (Fin 5 × Bool)) := [wE, wA1, wA2, wB1, wB2, wT, wSP]

@[expose] def kTabs : Array Table := (kWords.map tblW).toArray

@[expose] def kCheck : Bool :=
  enumOK 14 14 kTabs (mulClosureS 14 14 kTabs 4000) 384 &&
    kWords.all fun w => commT (tblW w) (tblW wJ)

@[expose] def rWords : List (List (Fin 5 × Bool)) := [wE, wA1, wA2, wB1, wB2]

@[expose] def rTabs : Array Table := (rWords.map tblW).toArray

@[expose] def rCheck : Bool := enumOK 14 14 rTabs (mulClosureS 14 14 rTabs 4000) 64

@[expose] def v2Perm : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 2] * List.formPerm [1, 3] * List.formPerm [5, 10] * List.formPerm [7, 11]

@[expose] def wTabs : List Table :=
  [idT 14, tbl14 bfJ, tbl14 u1P, tbl14 v2Perm, tbl14 (bfJ * u1P), tbl14 (bfJ * v2Perm),
    tbl14 (u1P * v2Perm), tbl14 (bfJ * u1P * v2Perm)]

@[expose] def inWT (T : Table) : Bool := wTabs.any fun S => tblEq 14 T S

@[expose] def wMemCheck : Bool :=
  inWT (tblW (invW wS ++ wJ ++ wS)) && epsT (tblW (invW wS ++ wJ ++ wS)) == 0 &&
    inWT (tblW (wA ++ wA)) && epsT (tblW (wA ++ wA)) == 0 &&
    !tblEq 14 (tblW (wA ++ wA)) (idT 14) && !tblEq 14 (tblW (wA ++ wA)) (tblW wJ)

@[expose] def vWord14 (m : ℕ) : List (Fin 5 × Bool) :=
  powW wJ (m % 2) ++ powW (wA1 ++ wB1) (m / 2 % 2) ++ powW (wA2 ++ wB2) (m / 4 % 2) ++
    powW wE (m / 8 % 2)

@[expose] def cvCheck : Bool :=
  (List.range 384).all fun k =>
    !(commT yEl[k]! (tblW wJ) && commT yEl[k]! (tblW (wA1 ++ wB1)) &&
      commT yEl[k]! (tblW (wA2 ++ wB2)) && commT yEl[k]! (tblW wE)) ||
      (List.range 16).any fun m => tblEq 14 yEl[k]! (tblW (vWord14 m))

@[expose] def swE (l : List ℤ) : List (Fin 6 × Bool) :=
  l.map fun z => (Fin.ofNat 6 (z.natAbs - 1), decide (0 < z))

@[expose] def relE : List (List (Fin 6 × Bool)) := relEL.map swE

@[expose] def eGens : Array Table :=
  #[#[2,0,6,7,8,10,1,4,3,5,13,14,15,9,12,11],
  #[4,8,7,0,6,12,3,1,2,15,14,5,13,11,9,10],
  #[1,6,0,7,8,9,2,4,3,13,5,14,15,10,12,11],
  #[3,8,7,6,0,11,4,1,2,15,14,13,5,12,9,10],
  #[0,1,2,3,4,13,6,7,8,10,9,12,11,5,15,14],
  #[5,9,10,11,12,0,13,14,15,1,2,3,4,6,7,8]]

@[expose] def eCheck : Bool := modelCheck 16 16 6 eGens relE 128

@[expose] def eT (w : List (Fin 6 × Bool)) : Table :=
  evalT 16 (fun i : Fin 6 => eGens[i.val]!) (fun i : Fin 6 => (eGens.map (invT 16))[i.val]!) w

@[expose] def actE (W : List (List ℤ)) (i : Fin 6) : List (Fin 6 × Bool) := swE (W.getD i.val [])

@[expose] def compF (α β : ℕ) (i : Fin 6) : List (Fin 6 × Bool) :=
  substW (actE (Wx α β)) (substW (actE Ws) (substW (actE (Wx α β)) (substW (actE Ws)
    (substW (actE (Wx α β)) (actE Ws i)))))

@[expose] def vgenE : List (List (Fin 6 × Bool)) := [swE [1, 1], swE [1, 3], swE [2, 4], swE [6]]

@[expose] def vWordE (m : ℕ) : List (Fin 6 × Bool) :=
  powW (swE [1, 1]) (m % 2) ++ powW (swE [1, 3]) (m / 2 % 2) ++ powW (swE [2, 4]) (m / 4 % 2) ++
    powW (swE [6]) (m / 8 % 2)

@[expose] def compFixV (α β : ℕ) : Bool :=
  vgenE.all fun w => tblEq 16 (eT (substW (compF α β) w)) (eT w)

@[expose] def compInnerV (α β : ℕ) : Bool :=
  (List.range 16).all fun m =>
    !((List.finRange 6).all fun i => tblEq 16 (eT (compF α β i))
        (eT (invW (vWordE m) ++ [(i, true)] ++ vWordE m))) ||
      (α == β && decide (m < 2))

@[expose] def lemma5Check : Bool :=
  sActOK && kCheck && rCheck && wMemCheck && cvCheck && eCheck &&
    ([0, 1].all fun α => [0, 1].all fun β => relNQCheck α β && compFixV α β && compInnerV α β) &&
    [0, 1].all fun α => [0, 1].all fun k => nCheck α k

end CFSG.EvenSporadicStandard.M12Std.Yosh
