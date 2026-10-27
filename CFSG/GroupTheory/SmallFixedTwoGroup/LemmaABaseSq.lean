module

public import Mathlib.Tactic.Group
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

private lemma mul_eq_one_or_z {T : Type*} [Group T] {z : T} (hz2 : z * z = 1) {a b : T}
    (ha : a = 1 ∨ a = z) (hb : b = 1 ∨ b = z) : a * b = 1 ∨ a * b = z := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hz2]

theorem sq_cases_of_card_sixteen {T : Type*} [Group T] [Finite T] (hcard : Nat.card T = 16)
    {z : T} (hz : z ∈ center T) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hnone : ¬ ∃ p : T, p * p ≠ 1 ∧ p * p ≠ z ∧ (p ^ 4 = 1 ∨ p ^ 4 = z)) :
    ∀ g : T, g * g = 1 ∨ g * g = z := by
  have horderz : orderOf z = 2 := orderOf_eq_prime (by rwa [pow_two]) hz1
  let N : Subgroup T := zpowers z
  haveI hNnormal : N.Normal := by
    apply Subgroup.normal_of_le_center
    show zpowers z ≤ center T
    exact Subgroup.zpowers_le.mpr hz
  have hNcard : Nat.card N = 2 := by
    show Nat.card (zpowers z) = 2
    rw [Nat.card_zpowers, horderz]
  have hquot : Nat.card (T ⧸ N) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcard, hNcard] at h
    omega
  intro g
  have h8 : g ^ 8 ∈ N := by
    have hpow : (QuotientGroup.mk' N g) ^ 8 = 1 := by
      have h := pow_card_eq_one' (G := T ⧸ N) (x := QuotientGroup.mk' N g)
      rwa [hquot] at h
    have hker : g ^ 8 ∈ (QuotientGroup.mk' N).ker := by
      rw [MonoidHom.mem_ker, map_pow, hpow]
    rwa [QuotientGroup.ker_mk' N] at hker
  have hg8 : g ^ 8 = 1 ∨ g ^ 8 = z :=
    (Subgroup.mem_zpowers_iff_of_orderOf_eq_two horderz).mp h8
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hgg : (g * g) * (g * g) = g ^ 4 := by
    rw [show g ^ 4 = g ^ 2 * g ^ 2 by group]
    simp only [pow_two]
  have hgg4 : (g * g) ^ 4 = g ^ 8 := by
    rw [← pow_two g, ← pow_mul]
  by_cases h4 : g ^ 4 = 1 ∨ g ^ 4 = z
  · exact hnone ⟨g, h1, h2, h4⟩
  · rw [not_or] at h4
    obtain ⟨h41, h42⟩ := h4
    refine hnone ⟨g * g, ?_, ?_, ?_⟩
    · rwa [hgg]
    · rwa [hgg]
    · rw [hgg4]; exact hg8

theorem conj_cases_of_sq_cases {T : Type*} [Group T] {z : T} (hz : z ∈ center T)
    (hz2 : z * z = 1) (hsq : ∀ g : T, g * g = 1 ∨ g * g = z) (g h : T) :
    g * h * g⁻¹ = h ∨ g * h * g⁻¹ = z * h := by
  have hcomm : ∀ w : T, w ∈ center T → ∀ x : T, w * x = x * w :=
    fun w hw x => (Subgroup.mem_center_iff.mp hw x).symm
  have hx4 : ∀ x : T, x ^ 4 = 1 := by
    intro x
    rw [show x ^ 4 = x ^ 2 * x ^ 2 by group]
    simp only [pow_two]
    rcases hsq x with hx | hx <;> rw [hx] <;> simp [hz2]
  have hmul4 : ∀ x : T, x * (x * (x * x)) = x ^ 4 := by
    intro x
    rw [show x ^ 4 = x ^ 2 * x ^ 2 by group]
    simp only [pow_two]
    group
  have hinv : ∀ x : T, x⁻¹ = x * (x * x) := by
    intro x
    apply inv_eq_of_mul_eq_one_right
    rw [hmul4 x, hx4 x]
  have hsqc : ∀ x : T, x * x ∈ center T := by
    intro x
    rcases hsq x with hx | hx
    · rw [hx]; exact Subgroup.one_mem _
    · rw [hx]; exact hz
  have hc : g * h * g⁻¹ * h⁻¹ = (g * h) * (g * h) * ((g * g) * (h * h)) := by
    rw [hinv g, hinv h]
    calc g * h * (g * (g * g)) * (h * (h * h))
        = ((g * h) * g) * ((g * g) * h) * (h * h) := by group
      _ = ((g * h) * g) * (h * (g * g)) * (h * h) := by
            rw [hcomm (g * g) (hsqc g) h]
      _ = (g * h) * (g * h) * ((g * g) * (h * h)) := by group
  have hcz : g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = z := by
    rw [hc]
    exact mul_eq_one_or_z hz2 (hsq (g * h)) (mul_eq_one_or_z hz2 (hsq g) (hsq h))
  have key : g * h * g⁻¹ = (g * h * g⁻¹ * h⁻¹) * h := by group
  rcases hcz with h1 | hz'
  · left; rw [h1, one_mul] at key; exact key
  · right; rw [hz'] at key; exact key

end CFSG.GroupTheory.SmallFixedTwoGroup
