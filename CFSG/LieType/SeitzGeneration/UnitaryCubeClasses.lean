module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.LieType.SeitzGeneration.NonCube

open Polynomial CFSG.LocalAnalysis.ComponentInitial

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem exists_primitive_cube_root (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) :
    ∃ ζ : K, ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧ h.bar ζ * ζ = 1 := by
  classical
  have hfin := h.finite
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Fintype.card K = ℓ ^ f * ℓ ^ f := by
    rw [← Nat.card_eq_fintype_card, h.card, two_mul, pow_add]
  have hd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hK]
    have h1 : ℓ ^ f * ℓ ^ f - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      simpa using this
    rw [h1]
    exact Dvd.dvd.mul_right hq3 _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hd
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hgK : (g : K) ^ 3 = 1 := by
    have := congrArg Units.val hg3
    simpa using this
  refine ⟨(g : K), hgK, ?_, ?_⟩
  · intro h1
    have : g = 1 := Units.ext h1
    rw [this, orderOf_one] at hg
    omega
  · rw [h.bar_apply, ← pow_succ]
    obtain ⟨m, hm⟩ := hq3
    rw [hm, pow_mul, hgK, one_pow]

theorem cube_dichotomy [Finite K] {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hcα : ¬ ∃ μ : K, μ ^ 3 = α) (hcβ : ¬ ∃ ν : K, ν ^ 3 = β) :
    (∃ ρ : K, ρ ^ 3 = α * β) ∨ (∃ ρ : K, ρ ^ 3 = α * β ^ 2) := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 α hα))
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 β hβ))
  have hcube : ∀ (a : K) (ha : a ≠ 0) (i : ℤ), g ^ i = Units.mk0 a ha → (3 : ℤ) ∣ i →
      ∃ μ : K, μ ^ 3 = a := by
    rintro a ha i hi ⟨k, rfl⟩
    refine ⟨((g ^ k : Kˣ) : K), ?_⟩
    have h1 : ((g ^ k : Kˣ) ^ 3 : Kˣ) = Units.mk0 a ha := by
      rw [← hi, ← _root_.zpow_natCast, ← _root_.zpow_mul]
      congr 1
      push_cast
      ring
    have := congrArg Units.val h1
    simpa using this
  have hi3 : ¬ (3 : ℤ) ∣ i := fun hd => hcα (hcube α hα i hi hd)
  have hj3 : ¬ (3 : ℤ) ∣ j := fun hd => hcβ (hcube β hβ j hj hd)
  have key : (3 : ℤ) ∣ i + j ∨ (3 : ℤ) ∣ i + 2 * j := by
    have h1 : i % 3 = 1 ∨ i % 3 = 2 := by omega
    have h2 : j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega
  rcases key with hk | hk
  · left
    refine hcube (α * β) (mul_ne_zero hα hβ) (i + j) ?_ hk
    rw [_root_.zpow_add, hi, hj]
    exact Units.ext (by simp)
  · right
    refine hcube (α * β ^ 2) (mul_ne_zero hα (pow_ne_zero 2 hβ)) (i + 2 * j) ?_ hk
    rw [_root_.zpow_add, hi, _root_.zpow_mul', hj]
    exact Units.ext (by simp)

theorem irreducible_X_pow_three_sub_C {α : K} (hc : ¬ ∃ μ : K, μ ^ 3 = α) :
    Irreducible (X ^ 3 - C α) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three fun b hb => hc ⟨b, hb⟩

end CFSG.LieType.SeitzGeneration.NonCube
