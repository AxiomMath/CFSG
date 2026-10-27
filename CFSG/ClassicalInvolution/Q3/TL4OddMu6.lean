module

public import CFSG.ClassicalInvolution.Q3.TL4OddBadW
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts28
public import CFSG.ClassicalInvolution.Q3.TL3T10

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Defs

variable {Y : Type} [Group Y]

@[expose] def LinkAEAt (R : Subgroup Y) (t : Y) : Prop :=
  ∃ m : ℕ, 5 ≤ m ∧ m ≤ 7 ∧ Nonempty (TC.Thin.AEIdent (coreLinkFam R t) m)

@[expose] def AE286Elt (t : Y) (J J' : Subgroup Y) : Prop :=
  ∃ y : Y, IsPGroup 3 (Subgroup.zpowers y) ∧ y ∈ Subgroup.centralizer ({t} : Set Y) ∧
    y ∈ Subgroup.normalizer (J : Set Y) ∧ y ∈ Subgroup.normalizer (J' : Set Y) ∧
    (∃ T : Subgroup Y, IsSylow2In T J ∧ y ∈ Subgroup.normalizer (T : Set Y) ∧
      ∃ x ∈ T, y * x * y⁻¹ ≠ x) ∧
    ∃ P : Subgroup Y, IsSylow2In P J' ∧ ∀ x ∈ P, y * x = x * y

end Defs

section Cit3


@[expose] def TightAE286ExistR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), NoGNbr R t J →
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J → LinkAEAt R t → AE286Elt t J J'

@[expose] def TightAE286NoneR (r n : ℕ) : Prop :=
  Model117 → Model117Pair →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), NoGNbr R t J →
      ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J → LinkAEAt R t →
          ¬ AE286Elt t J J'

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem not_linkAEAt_of_noGNbr (h117 : Model117) (h117p : Model117Pair)
    (hE : TightAE286ExistR r n) (hN : TightAE286NoneR r n) (hL : TightLargeHypR r n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R))) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) (hbad : NoGNbr R t J)
    {J' : Subgroup Y} (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hJJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) : ¬ LinkAEAt R t :=
  fun hAE => hN h117 h117p Y R S t hL hc J hJ hbad J' hJ' hJJ' hAE
    (hE Y R S t hL hc J hJ hbad J' hJ' hJJ' hAE)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
