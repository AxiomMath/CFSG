module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcRoot
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRows

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Rows


theorem a2l_datum_of_untwisted {X : Type} [Group X] {τ : Tag} {f : ℕ} (hf : 2 ≤ f)
    (h : UntwistedChevalleyModel X τ (3 ^ f)) : a2lDatum X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ h
  have : CharP K 3 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    norm_num
  have h9 : 9 ≤ Nat.card K := by
    rw [hK]
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact a2lDatum_of_mulEquiv e.symm (a2l_datum_adjoint hK2 h9)

theorem a2l_datum_of_untwisted_of_three {X : Type} [Group X] {τ : Tag} {f : ℕ} (hf : 1 ≤ f)
    (h : UntwistedChevalleyModel X τ (3 ^ f)) (h3 : f = 1 → a2lDatum X) : a2lDatum X := by
  rcases Nat.lt_or_ge f 2 with hlt | hge
  · obtain rfl : f = 1 := by omega
    exact h3 rfl
  · exact a2l_datum_of_untwisted hge h

theorem a2lRowG2_holds : a2lRowG2 := by
  intro X _ _ f hf hS
  exact a2l_datum_of_untwisted (τ := .G2) hf
    (hS.chevalleyExceptionalModel (by decide)).2

@[expose] def a2lF4Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .F4 0 3 1 → a2lDatum X

@[expose] def a2lE6Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .E6 0 3 1 → a2lDatum X

@[expose] def a2lE7Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .E7 0 3 1 → a2lDatum X

@[expose] def a2lE8Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .E8 0 3 1 → a2lDatum X

theorem a2lRowF4_of_three (h3 : a2lF4Three) : a2lRowF4 := by
  intro X _ _ f hS
  have hc := hS.chevalleyExceptionalModel (by decide)
  refine a2l_datum_of_untwisted_of_three (τ := .F4) hc.1.2.1 hc.2 fun h1 => ?_
  subst h1
  exact h3 X hS

theorem a2lRowE6_of_three (h3 : a2lE6Three) : a2lRowE6 := by
  intro X _ _ f hS
  have hc := hS.chevalleyExceptionalModel (by decide)
  refine a2l_datum_of_untwisted_of_three (τ := .E6) hc.1.2.1 hc.2 fun h1 => ?_
  subst h1
  exact h3 X hS

theorem a2lRowE7_of_three (h3 : a2lE7Three) : a2lRowE7 := by
  intro X _ _ f hS
  have hc := hS.chevalleyExceptionalModel (by decide)
  refine a2l_datum_of_untwisted_of_three (τ := .E7) hc.1.2.1 hc.2 fun h1 => ?_
  subst h1
  exact h3 X hS

theorem a2lRowE8_of_three (h3 : a2lE8Three) : a2lRowE8 := by
  intro X _ _ f hS
  have hc := hS.chevalleyExceptionalModel (by decide)
  refine a2l_datum_of_untwisted_of_three (τ := .E8) hc.1.2.1 hc.2 fun h1 => ?_
  subst h1
  exact h3 X hS

end Rows

end CFSG.OddStandard.SmallF3.HypA2Leaves
