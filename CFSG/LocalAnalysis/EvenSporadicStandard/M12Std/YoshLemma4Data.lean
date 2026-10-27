module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshBaseData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshQData

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable

@[expose] def sw (l : List ℤ) : List (Fin 5 × Bool) :=
  l.map fun z => (Fin.ofNat 5 z.natAbs, decide (0 < z))

@[expose] def wE : List (Fin 5 × Bool) := [(0, true)]
@[expose] def wA : List (Fin 5 × Bool) := sw [4, 3, 4, -3, 4, -1, -3, -3]
@[expose] def wB : List (Fin 5 × Bool) := sw [3, 3, 4, 3, 4, -3, 4, -1, -3, 1]
@[expose] def wU : List (Fin 5 × Bool) := sw [-1, -1, -1, -1, -2, 1]
@[expose] def wS : List (Fin 5 × Bool) :=
  sw [-2, 4, -1, -2, 4, 1, 2, 4, -1, 4, 3, 4, 3, 4, 1, 1, 2, 3]
@[expose] def wR : List (Fin 5 × Bool) := sw [-2, -3]

@[expose] def sub4 (i : Fin 8) : List (Fin 5 × Bool) :=
  match i with
  | 0 => wE
  | 1 => wA
  | 2 => wB
  | 3 => wU
  | 4 => wS
  | 5 => wR
  | _ => []

@[expose] def zWord (α β : ℕ) : List (Fin 5 × Bool) := powW wU α ++ powW wJ β ++ powW wE β

@[expose] def relPOK : Bool :=
  rel4P.all fun r => tblEq 14 (tblW (substW sub4 r)) (idT 14)

@[expose] def stepIs (α : ℕ) (wm y rhs : List (Fin 5 × Bool)) : Bool :=
  match stepW α wm y with
  | some f => tblEq 14 (tblW f) (tblW rhs)
  | none => false

@[expose] def xIs (α : ℕ) (ws y rhs : List (Fin 5 × Bool)) : Bool :=
  match xAct α ws y with
  | some f => tblEq 14 (tblW f) (tblW rhs)
  | none => false

@[expose] def stepOK (α : ℕ) : Bool :=
  epsT (tblW wS) == 0 && (tblEq 14 (tblW (wS ++ wS ++ wS)) (idT 14) &&
  (tblEq 14 (tblW (wA ++ wA ++ wB ++ wB)) (tblW wJ) &&
  (tblEq 14 (tblW (invW wR ++ wS ++ wR)) (tblW (invW wS)) &&
  (stepIs α [] wA (wA ++ powW wJ α) && (stepIs α [] wB (wB ++ powW wJ α) &&
  (stepIs α [] wU wU && (stepIs α [] wR wR &&
  (stepIs α (invW wS) wE (wE ++ wA ++ wA) && (stepIs α (invW wS) wA wA &&
  (stepIs α (invW wS) wB (wB ++ powW (wA ++ wA) α) && (stepIs α (invW wS) wU wU &&
  stepIs α (invW wS) wJ wJ))))))))))) 

@[expose] def zOK (α β : ℕ) : Bool :=
  tblEq 14 (tblW (zWord α β ++ zWord α β)) (idT 14) &&
    (stepIs α wS (zWord α β) (zWord α β ++ powW (wB ++ wB) β) &&
    tblEq 14 (tblW (zWord α β ++ powW (wB ++ wB) β ++ zWord α β)) (tblW (powW (wB ++ wB) β)))

@[expose] def xRes (α : ℕ) (y : List (Fin 5 × Bool)) : List (Fin 5 × Bool) :=
  (xAct α wS y).getD []

@[expose] def xDefined (α : ℕ) : Bool := [wA, wB, wU].all fun y => (xAct α wS y).isSome

@[expose] def xOK (α : ℕ) : Bool := xDefined α && (xIs α wS wE wE && xIs α wS wJ wJ)

@[expose] def condX (α : ℕ) (T : Table) : Bool :=
  [wA, wB, wU].all fun y => tblEq 14 (compT 14 T (tblW y)) (compT 14 (tblW (xRes α y)) T)

@[expose] def commS (T : Table) : Bool :=
  commT (compT 14 (compT 14 (tblW (invW wS)) T) (tblW wS)) (tblW wJ)

@[expose] def sEqn (α : ℕ) (T : Table) : Bool :=
  let T' := compT 14 (compT 14 (tblW (invW wS)) T) (tblW wS)
  tblEq 14 T' (compT 14 T (powT 14 (epsT T' + α * lamT T') (tblW (wS ++ wJ ++ invW wS))))

@[expose] def xDetermined : Bool :=
  [0, 1].all fun α => (List.range 384).all fun k =>
    !condX α yEl[k]! || (commS yEl[k]! &&
      (!sEqn α yEl[k]! || [0, 1].any fun β => tblEq 14 yEl[k]! (tblW (zWord α β))))

@[expose] def lemma4Check : Bool :=
  relPOK && ([0, 1].all (fun α => stepOK α && (xOK α && [0, 1].all fun β => zOK α β)) &&
    (xDetermined &&
    [0, 1].all fun α => [0, 1].all fun β => qCheck α β))

end CFSG.EvenSporadicStandard.M12Std.Yosh
