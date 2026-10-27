module

public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedCore

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalFiveFixed

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p : ι}

theorem base_fixed_arith {M : ℕ} (hM : 2 ≤ M) {u v w o z : ℤ} (h1 : 1 + u - v + w = 0)
    (h2 : -1 - u - v + w + 2 * o = 0) (h3 : 1 - u - v - w + 2 * z = 6)
    (hN : 1 + u * u + v * v + w * w + z * z + M * (o * o) ≤ 7) :
    u = -1 ∧ o = 0 ∧ ((v = -1 ∧ w = -1 ∧ z = 1) ∨ (v = 0 ∧ w = 0 ∧ z = 2)) := by
  have hw : w = v - u - 1 := by linarith
  have ho : o = 1 + u := by linarith
  have hz : z = v + 2 := by linarith
  subst hw ho hz
  have hM' : (2 : ℤ) ≤ M := by exact_mod_cast hM
  have hsq : 0 ≤ (1 + u) * (1 + u) := mul_self_nonneg _
  have hMo : 2 * ((1 + u) * (1 + u)) ≤ M * ((1 + u) * (1 + u)) := by nlinarith
  have q1 := mul_self_nonneg u
  have q2 := mul_self_nonneg v
  have q3 := mul_self_nonneg (v - u - 1)
  have q4 := mul_self_nonneg (v + 2)
  have hu1 : (1 + u) * (1 + u) ≤ 3 := by nlinarith
  have hu2 : -2 ≤ u := by nlinarith
  have hu3 : u ≤ 0 := by nlinarith
  have hcases : u = -2 ∨ u = -1 ∨ u = 0 := by omega
  rcases hcases with rfl | rfl | rfl
  · have q5 := mul_self_nonneg (v + 1)
    nlinarith
  · have hv1 : -2 < v := by nlinarith
    have hv2 : v < 1 := by nlinarith
    refine ⟨rfl, by ring, ?_⟩
    have hvc : v = -1 ∨ v = 0 := by omega
    rcases hvc with rfl | rfl
    · left
      norm_num
    · right
      norm_num
  · have q5 := mul_self_nonneg (3 * v + 1)
    nlinarith

omit [DecidableEq ι] in
theorem base_fixed_coords {κ' : Type*} {J : Finset κ'} {χ : κ' → ι} {M : ℕ} (hM : 2 ≤ M)
    (hJ : M ≤ J.card) {A Bq Dq ω : ι} {σ τ₀ κ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hτ₀ : τ₀ = 1 ∨ τ₀ = -1) (hκ : κ = 1 ∨ κ = -1) {b : ι → ℤ} (hbp : b p = 1)
    (h1 : b p + σ * b A - τ₀ * b Bq + κ * b Dq = 0)
    (h2 : ∀ j ∈ J, -b p - σ * b A - τ₀ * b Bq + κ * b Dq + 2 * σ * b (χ j) = 0)
    (h3 : b p - σ * b A - τ₀ * b Bq - κ * b Dq + 2 * τ₀ * b ω = 6)
    (hN : b p * b p + b A * b A + b Bq * b Bq + b Dq * b Dq + b ω * b ω +
      ∑ j ∈ J, b (χ j) * b (χ j) ≤ 7) :
    b A = -σ ∧ (∀ j ∈ J, b (χ j) = 0) ∧
      ((b Bq = -τ₀ ∧ b Dq = -κ ∧ b ω = τ₀) ∨ (b Bq = 0 ∧ b Dq = 0 ∧ b ω = 2 * τ₀)) := by
  have hodd : ∀ j ∈ J, b (χ j) = σ * (1 + σ * b A) := by
    intro j hj
    have e := h2 j hj
    rcases hσ with rfl | rfl <;> rcases hτ₀ with rfl | rfl <;> rcases hκ with rfl | rfl <;>
      linarith
  set o' := σ * (1 + σ * b A) with ho'
  have hJsum : ∑ j ∈ J, b (χ j) * b (χ j) = J.card * (o' * o') := by
    rw [Finset.sum_congr rfl fun j hj => by rw [hodd j hj]]
    simp
  have hJ' : (M : ℤ) * (o' * o') ≤ J.card * (o' * o') :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hJ) (mul_self_nonneg o')
  rw [hJsum, hbp] at hN
  rw [hbp] at h1 h3
  have hN' : 1 + (σ * b A) * (σ * b A) + (τ₀ * b Bq) * (τ₀ * b Bq) + (κ * b Dq) * (κ * b Dq) +
      (τ₀ * b ω) * (τ₀ * b ω) + M * ((σ * o') * (σ * o')) ≤ 7 := by
    rw [ho'] at hJ' hN ⊢
    rcases hσ with rfl | rfl <;> rcases hτ₀ with rfl | rfl <;> rcases hκ with rfl | rfl <;>
      linarith
  obtain ⟨hu, ho, hvwz⟩ := base_fixed_arith hM (u := σ * b A) (v := τ₀ * b Bq)
    (w := κ * b Dq) (o := σ * o') (z := τ₀ * b ω) (by linarith)
    (by rw [ho']; rcases hσ with rfl | rfl <;> linarith) (by linarith) hN'
  have hbA : b A = -σ := by rcases hσ with rfl | rfl <;> linarith
  refine ⟨hbA, fun j hj => ?_, ?_⟩
  · rw [hodd j hj, ho', hbA]
    rcases hσ with rfl | rfl <;> norm_num
  · rcases hvwz with ⟨hv, hw, hz⟩ | ⟨hv, hw, hz⟩
    · left
      refine ⟨?_, ?_, ?_⟩ <;> [rcases hτ₀ with rfl | rfl; rcases hκ with rfl | rfl;
        rcases hτ₀ with rfl | rfl] <;> linarith
    · right
      refine ⟨?_, ?_, ?_⟩ <;> [rcases hτ₀ with rfl | rfl; rcases hκ with rfl | rfl;
        rcases hτ₀ with rfl | rfl] <;> linarith

end CFSG.Wreathed.ConditionalCompleteBase
