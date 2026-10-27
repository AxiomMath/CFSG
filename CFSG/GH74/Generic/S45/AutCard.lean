module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.GH74.Generic.S45

open Subgroup

theorem card_range_eq_of_ker_eq {M A₁ A₂ : Type*} [Group M] [Group A₁] [Group A₂]
    (ρ₁ : M →* A₁) (ρ₂ : M →* A₂) (h : ρ₁.ker = ρ₂.ker) :
    Nat.card ρ₁.range = Nat.card ρ₂.range := by
  have e₁ := Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ₁).toEquiv
  have e₂ := Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ₂).toEquiv
  rw [← e₁, ← e₂]
  exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq h).toEquiv

theorem card_range_normalizerMonoidHom_mul {X : Type*} [Group X] [Finite X] (H : Subgroup X) :
    Nat.card H.normalizerMonoidHom.range * Nat.card (centralizer (H : Set X)) =
      Nat.card (normalizer (H : Set X)) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup H.normalizerMonoidHom.ker
  have e := Nat.card_congr (QuotientGroup.quotientKerEquivRange H.normalizerMonoidHom).toEquiv
  have hker : H.normalizerMonoidHom.ker =
      (centralizer (H : Set X)).subgroupOf (normalizer (H : Set X)) := by
    ext n
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centralizer_iff]
    constructor
    · intro h g hg
      have := congrArg (fun a : ↥H => (a : X)) (DFunLike.congr_fun h ⟨g, hg⟩)
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    · intro h
      ext a
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
      exact mul_inv_eq_iff_eq_mul.2 (h a a.2).symm
  have hcard : Nat.card ↥H.normalizerMonoidHom.ker = Nat.card (centralizer (H : Set X)) := by
    rw [hker]
    have hle : centralizer (H : Set X) ≤ normalizer (H : Set X) :=
      Subgroup.centralizer_le_normalizer _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  rw [← hcard, ← e]
  exact h1.symm

end CFSG.GH74.Generic.S45
