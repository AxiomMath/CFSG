module

public import CFSG.GH74.Uniqueness.Section15Aux

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem trans_of_free_of_card {A P N : Subgroup X} (_hNP : N ≤ P)
    (hAP : ∀ a ∈ A, ∀ x ∈ P, a * x * a⁻¹ ∈ P) (hAN : ∀ a ∈ A, ∀ x ∈ N, a * x * a⁻¹ ∈ N)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ x ∈ P, x⁻¹ * (a * x * a⁻¹) ∈ N → x ∈ N)
    (hcard : Nat.card A = (N.subgroupOf P).index - 1) :
    ∀ x ∈ P, x ∉ N → ∀ y ∈ P, y ∉ N → ∃ a ∈ A, y⁻¹ * (a * x * a⁻¹) ∈ N := by
  classical
  intro x hxP hxN y hyP hyN
  have hmk : ∀ w : ↥P, (QuotientGroup.mk w : ↥P ⧸ N.subgroupOf P) = QuotientGroup.mk 1 ↔
      (w : X) ∈ N := by
    intro w
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  have hconjP : ∀ a : ↥A, (a : X) * x * (a : X)⁻¹ ∈ P := fun a => hAP a a.2 x hxP
  let g : ↥A → {q : ↥P ⧸ N.subgroupOf P // q ≠ QuotientGroup.mk 1} := fun a =>
    ⟨QuotientGroup.mk ⟨(a : X) * x * (a : X)⁻¹, hconjP a⟩, by
      intro h
      rw [hmk] at h
      apply hxN
      have := hAN (a : X)⁻¹ (A.inv_mem a.2) _ h
      simpa [mul_assoc] using this⟩
  have hinj : Function.Injective g := by
    intro a b hab
    have h1 : (QuotientGroup.mk ⟨(a : X) * x * (a : X)⁻¹, hconjP a⟩ : ↥P ⧸ N.subgroupOf P) =
        QuotientGroup.mk ⟨(b : X) * x * (b : X)⁻¹, hconjP b⟩ := congrArg Subtype.val hab
    have h2 := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    have h3 : x⁻¹ * (((a : X)⁻¹ * b) * x * ((a : X)⁻¹ * b)⁻¹) ∈ N := by
      have h4 := hAN (a : X)⁻¹ (A.inv_mem a.2) _ h2
      have e : (a : X)⁻¹ * (((a : X) * x * (a : X)⁻¹)⁻¹ * ((b : X) * x * (b : X)⁻¹)) *
          (a : X)⁻¹⁻¹ = x⁻¹ * (((a : X)⁻¹ * b) * x * ((a : X)⁻¹ * b)⁻¹) := by group
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
      rw [e] at h4
      exact h4
    by_contra hne
    have hc : (a : X)⁻¹ * b ≠ 1 := by
      intro h
      exact hne (Subtype.ext (inv_mul_eq_one.mp h))
    exact hxN (hfree _ (A.mul_mem (A.inv_mem a.2) b.2) hc x hxP h3)
  have hcardT : Nat.card {q : ↥P ⧸ N.subgroupOf P // q ≠ QuotientGroup.mk 1} ≤ Nat.card ↥A := by
    rw [card_subtype_ne_eq_sub_one, hcard, Subgroup.index_eq_card]
  have hbij := hinj.bijective_of_nat_card_le hcardT
  obtain ⟨a, ha⟩ := hbij.2 ⟨QuotientGroup.mk ⟨y, hyP⟩, by
    intro h
    exact hyN ((hmk _).mp h)⟩
  refine ⟨(a : X), a.2, ?_⟩
  have h1 := congrArg Subtype.val ha
  have h2 := QuotientGroup.eq.mp h1.symm
  rw [Subgroup.mem_subgroupOf] at h2
  simpa using h2

end CFSG.GH74.Uniqueness
