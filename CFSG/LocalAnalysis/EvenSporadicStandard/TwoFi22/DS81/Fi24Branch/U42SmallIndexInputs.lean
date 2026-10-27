module

public import Mathlib
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.NativeChecks2

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42SmallIndex

open CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43

@[expose] def z0 : Equiv.Perm (Fin 45) :=
  tab <| List.formPerm [0, 33, 31] * List.formPerm [1, 34, 29] * List.formPerm [2, 32, 30] *
    List.formPerm [3, 18, 36] * List.formPerm [4, 16, 37] * List.formPerm [5, 17, 38] *
    List.formPerm [6, 35, 14] * List.formPerm [7, 13, 15] * List.formPerm [9, 41, 23] *
    List.formPerm [10, 39, 24] * List.formPerm [11, 40, 22] * List.formPerm [26, 28, 27]

@[expose] def pa : Equiv.Perm (Fin 45) :=
  tab <| List.formPerm [1, 18, 39] * List.formPerm [2, 22, 37] * List.formPerm [3, 10, 29] *
    List.formPerm [4, 32, 11] * List.formPerm [5, 38, 17] * List.formPerm [6, 13, 27] *
    List.formPerm [7, 28, 14] * List.formPerm [8, 42, 19] * List.formPerm [9, 41, 23] *
    List.formPerm [12, 43, 21] * List.formPerm [15, 26, 35] * List.formPerm [16, 30, 40] *
    List.formPerm [20, 25, 44] * List.formPerm [24, 34, 36]

@[expose] def pb : Equiv.Perm (Fin 45) :=
  tab <| List.formPerm [0, 9, 38] * List.formPerm [1, 18, 10] * List.formPerm [2, 30, 32] *
    List.formPerm [3, 24, 29] * List.formPerm [5, 33, 41] * List.formPerm [6, 27, 15] *
    List.formPerm [7, 35, 26] * List.formPerm [8, 21, 44] * List.formPerm [11, 40, 22] *
    List.formPerm [12, 20, 42] * List.formPerm [13, 14, 28] * List.formPerm [17, 31, 23] *
    List.formPerm [19, 43, 25] * List.formPerm [34, 36, 39]

@[expose] def bl : List (Equiv.Perm (Fin 45)) :=
  (elemsTab QP45).filter fun g => decide (g * z0 = z0 * g)

@[expose] def closureStep (gens S : List (Equiv.Perm (Fin 45))) : List (Equiv.Perm (Fin 45)) :=
  S.foldl (fun acc x => gens.foldl (fun acc' g =>
    if tab (g * x) ∈ acc' then acc' else acc' ++ [tab (g * x)]) acc) S

@[expose] def closureList (gens : List (Equiv.Perm (Fin 45))) :
    ℕ → List (Equiv.Perm (Fin 45)) → List (Equiv.Perm (Fin 45))
  | 0, S => S
  | n + 1, S => closureList gens n (closureStep gens S)

@[expose] def pcl : List (Equiv.Perm (Fin 45)) := closureList [pa, pb] 30 [1]

@[expose] def pl : List (Equiv.Perm (Fin 45)) := bl.filter fun g => decide (g ∈ pcl)

@[expose] def plMulCheck : Bool :=
  pl.all fun x => pl.all fun y => decide (x * y ∈ pl)

@[expose] def plExpCheck : Bool :=
  pl.all fun x => decide (x ^ 3 = 1)

@[expose] def blNormCheck : Bool :=
  bl.all fun x => pl.all fun p => decide (x * p * x⁻¹ ∈ pl)

@[expose] def cosetReps (T : List (Equiv.Perm (Fin 45))) : List (Equiv.Perm (Fin 45)) :=
  T.foldl (fun reps x =>
    if reps.any (fun r => decide (x * r⁻¹ ∈ pl)) then reps else reps ++ [x]) []

@[expose] def conjSet (a : Equiv.Perm (Fin 45)) : List (Equiv.Perm (Fin 45)) :=
  bl.filter fun x => decide (x * a * x⁻¹ = a) || decide (x * a * x⁻¹ = a⁻¹)

@[expose] def cosetCheck (a : Equiv.Perm (Fin 45)) : Bool :=
  let T := conjSet a
  let reps := cosetReps T
  decide (reps.length ≤ 6) && T.all fun x => reps.any fun r => decide (x * r⁻¹ ∈ pl)

@[expose] def zDataCheck (z : Equiv.Perm (Fin 45)) : Bool :=
  decide (z ≠ 1) && (pl.any fun x => pl.any fun y => decide (z = x * y * x⁻¹ * y⁻¹)) &&
    (pl.all fun a => decide (a = 1) || decide (a = z) || decide (a⁻¹ = z) || cosetCheck a)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42SmallIndex
