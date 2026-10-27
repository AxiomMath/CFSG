module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FlatRelative

@[expose] noncomputable def weightedSum {ι : Type*} (s : Finset ι) (w : ι → ℂ) : (ι → ℤ) →+ ℂ where
  toFun f := ∑ χ ∈ s, w χ * (f χ : ℂ)
  map_zero' := by simp
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]

theorem weightedSum_apply {ι : Type*} (s : Finset ι) (w : ι → ℂ) (f : ι → ℤ) :
    weightedSum s w f = ∑ χ ∈ s, w χ * (f χ : ℂ) := rfl

theorem weightedSum_single {ι : Type*} {s : Finset ι} (w : ι → ℂ) {i : ι} (hi : i ∈ s) (x : ℤ) :
    weightedSum s w (Pi.single i x) = w i * x := by
  rw [weightedSum_apply, Finset.sum_eq_single i (fun j _ hj => by
      rw [Pi.single_eq_of_ne hj, Int.cast_zero, mul_zero]) (fun h => absurd hi h),
    Pi.single_eq_same]

theorem div_mul_sign {δ : ℂ} (hδ : δ = 1 ∨ δ = -1) (x f : ℂ) : x / f * δ = x / (δ * f) := by
  rcases hδ with rfl | rfl
  · rw [mul_one, one_mul]
  · rw [mul_neg_one, neg_one_mul, div_neg]

theorem weight_sign_mul {δ s : ℂ} (hδ : δ = 1 ∨ δ = -1) (hs : s ^ 2 = 1) (x f : ℂ) :
    s * x * (s * x) / f * δ = x ^ 2 / (δ * f) := by
  rw [show s * x * (s * x) = s ^ 2 * x ^ 2 by ring, hs, one_mul, div_mul_sign hδ]

theorem weight_neg_sign_mul {δ s : ℂ} (hδ : δ = 1 ∨ δ = -1) (hs : s ^ 2 = 1) (x f : ℂ) :
    -(s * x) * -(s * x) / f * δ = x ^ 2 / (δ * f) := by
  rw [neg_mul_neg, weight_sign_mul hδ hs]

theorem weight_sign {δ s : ℂ} (hδ : δ = 1 ∨ δ = -1) (hs : s ^ 2 = 1) (f : ℂ) :
    s * s / f * δ = 1 / (δ * f) := by
  rw [← sq, hs, div_mul_sign hδ]

theorem cast_sign {x : ℤ} (hx : x = 1 ∨ x = -1) : (x : ℂ) = 1 ∨ (x : ℂ) = -1 := by
  rcases hx with rfl | rfl <;> simp

theorem cast_sign_sq {x : ℤ} (hx : x = 1 ∨ x = -1) : (x : ℂ) ^ 2 = 1 := by
  rcases hx with rfl | rfl <;> simp

theorem weighted_first {q ε β δ₀ δ₁ δ₂ δ₃ f₀ f₁ f₂ f₃ : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hβ : β = 1 ∨ β = -1) (s₀ : δ₀ = 1 ∨ δ₀ = -1) (s₁ : δ₁ = 1 ∨ δ₁ = -1)
    (s₂ : δ₂ = 1 ∨ δ₂ = -1) (s₃ : δ₃ = 1 ∨ δ₃ = -1) (hf₀ : f₀ ≠ 0) (hf₁ : f₁ ≠ 0)
    (hf₂ : f₂ ≠ 0) (hf₃ : f₃ ≠ 0)
    (h : (β : ℂ) * ((δ₀ : ℂ) * ε * q * (δ₀ * ε * q) / f₀ * δ₀ + -(δ₁ : ℂ) * -δ₁ / f₁ * δ₁ -
      -((δ₂ : ℂ) * (2 + ε * q)) * -(δ₂ * (2 + ε * q)) / f₂ * δ₂ -
      (δ₃ : ℂ) * (1 + 2 * ε * q) * (δ₃ * (1 + 2 * ε * q)) / f₃ * δ₃) = 0) :
    δ₀ * f₀ * (δ₂ * f₂) * -(δ₃ * f₃) + q ^ 2 * (δ₁ * f₁) * (δ₂ * f₂) * -(δ₃ * f₃) -
      (2 + ε * q) ^ 2 * (δ₁ * f₁) * (δ₀ * f₀) * -(δ₃ * f₃) +
      (1 + 2 * ε * q) ^ 2 * (δ₁ * f₁) * (δ₀ * f₀) * (δ₂ * f₂) = 0 := by
  have e₀ := cast_sign s₀
  have e₁ := cast_sign s₁
  have e₂ := cast_sign s₂
  have e₃ := cast_sign s₃
  have hβ0 : (β : ℂ) ≠ 0 := by rcases hβ with rfl | rfl <;> norm_num
  have hs0 : ((δ₀ : ℂ) * ε) ^ 2 = 1 := by rw [mul_pow, cast_sign_sq s₀, cast_sign_sq hε, one_mul]
  have hs1 : (-(δ₁ : ℂ)) ^ 2 = 1 := by rw [neg_sq, cast_sign_sq s₁]
  rw [weight_sign_mul e₀ hs0, weight_sign e₁ hs1, weight_neg_sign_mul e₂ (cast_sign_sq s₂),
    weight_sign_mul e₃ (cast_sign_sq s₃)] at h
  have hin := (mul_eq_zero.mp h).resolve_left hβ0
  have n₀ : (δ₀ : ℂ) ≠ 0 := by rcases e₀ with h | h <;> rw [h] <;> norm_num
  have n₁ : (δ₁ : ℂ) ≠ 0 := by rcases e₁ with h | h <;> rw [h] <;> norm_num
  have n₂ : (δ₂ : ℂ) ≠ 0 := by rcases e₂ with h | h <;> rw [h] <;> norm_num
  have n₃ : (δ₃ : ℂ) ≠ 0 := by rcases e₃ with h | h <;> rw [h] <;> norm_num
  have m₀ : (f₀ : ℂ) ≠ 0 := by exact_mod_cast hf₀
  have m₁ : (f₁ : ℂ) ≠ 0 := by exact_mod_cast hf₁
  have m₂ : (f₂ : ℂ) ≠ 0 := by exact_mod_cast hf₂
  have m₃ : (f₃ : ℂ) ≠ 0 := by exact_mod_cast hf₃
  have key : ((q : ℂ) ^ 2 / (δ₀ * f₀) + 1 / (δ₁ * f₁) - (2 + ε * q) ^ 2 / (δ₂ * f₂) -
      (1 + 2 * ε * q) ^ 2 / (δ₃ * f₃)) * ((δ₀ * f₀) * (δ₁ * f₁) * (δ₂ * f₂) * (δ₃ * f₃)) =
      (q : ℂ) ^ 2 * (δ₁ * f₁) * (δ₂ * f₂) * (δ₃ * f₃) + (δ₀ * f₀) * (δ₂ * f₂) * (δ₃ * f₃) -
        (2 + ε * q) ^ 2 * (δ₀ * f₀) * (δ₁ * f₁) * (δ₃ * f₃) -
        (1 + 2 * ε * q) ^ 2 * (δ₀ * f₀) * (δ₁ * f₁) * (δ₂ * f₂) := by
    field_simp
  rw [hin, zero_mul] at key
  have hC : ((δ₀ * f₀ * (δ₂ * f₂) * -(δ₃ * f₃) + q ^ 2 * (δ₁ * f₁) * (δ₂ * f₂) * -(δ₃ * f₃) -
      (2 + ε * q) ^ 2 * (δ₁ * f₁) * (δ₀ * f₀) * -(δ₃ * f₃) +
      (1 + 2 * ε * q) ^ 2 * (δ₁ * f₁) * (δ₀ * f₀) * (δ₂ * f₂) : ℤ) : ℂ) = 0 := by
    push_cast
    linear_combination key
  exact_mod_cast hC

theorem weighted_second {q ε δ₀ δ₁ δ₂ δ₃ f₀ f₁ f₂ f₃ : ℤ} (hε : ε = 1 ∨ ε = -1)
    (s₀ : δ₀ = 1 ∨ δ₀ = -1) (s₁ : δ₁ = 1 ∨ δ₁ = -1) (s₂ : δ₂ = 1 ∨ δ₂ = -1)
    (s₃ : δ₃ = 1 ∨ δ₃ = -1) (hf₀ : f₀ ≠ 0) (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) (hf₃ : f₃ ≠ 0)
    (h : (δ₀ : ℂ) * ε * q * (δ₀ * ε * q) / f₀ * δ₀ + -(δ₁ : ℂ) * -δ₁ / f₁ * δ₁ +
      -((δ₂ : ℂ) * (2 + ε * q)) * -(δ₂ * (2 + ε * q)) / f₂ * δ₂ +
      (δ₃ : ℂ) * (1 + 2 * ε * q) * (δ₃ * (1 + 2 * ε * q)) / f₃ * δ₃ -
      (δ₂ : ℂ) * ε * q * (δ₂ * ε * q) / f₂ * δ₂ - (δ₂ : ℂ) * ε * q * (δ₂ * ε * q) / f₂ * δ₂ -
      -(δ₃ : ℂ) * -δ₃ / f₃ * δ₃ - -(δ₃ : ℂ) * -δ₃ / f₃ * δ₃ = 0) :
    -(δ₀ * f₀ * (δ₂ * f₂) * -(δ₃ * f₃)) - q ^ 2 * (δ₁ * f₁) * (δ₂ * f₂) * -(δ₃ * f₃) +
      (2 * q ^ 2 - (2 + ε * q) ^ 2) * (δ₁ * f₁) * (δ₀ * f₀) * -(δ₃ * f₃) +
      ((1 + 2 * ε * q) ^ 2 - 2) * (δ₁ * f₁) * (δ₀ * f₀) * (δ₂ * f₂) = 0 := by
  have e₀ := cast_sign s₀
  have e₁ := cast_sign s₁
  have e₂ := cast_sign s₂
  have e₃ := cast_sign s₃
  have hs0 : ((δ₀ : ℂ) * ε) ^ 2 = 1 := by rw [mul_pow, cast_sign_sq s₀, cast_sign_sq hε, one_mul]
  have hs2 : ((δ₂ : ℂ) * ε) ^ 2 = 1 := by rw [mul_pow, cast_sign_sq s₂, cast_sign_sq hε, one_mul]
  have hs1 : (-(δ₁ : ℂ)) ^ 2 = 1 := by rw [neg_sq, cast_sign_sq s₁]
  have hs3 : (-(δ₃ : ℂ)) ^ 2 = 1 := by rw [neg_sq, cast_sign_sq s₃]
  rw [weight_sign_mul e₀ hs0, weight_sign e₁ hs1, weight_neg_sign_mul e₂ (cast_sign_sq s₂),
    weight_sign_mul e₃ (cast_sign_sq s₃), weight_sign_mul e₂ hs2, weight_sign e₃ hs3] at h
  have n₀ : (δ₀ : ℂ) ≠ 0 := by rcases e₀ with h | h <;> rw [h] <;> norm_num
  have n₁ : (δ₁ : ℂ) ≠ 0 := by rcases e₁ with h | h <;> rw [h] <;> norm_num
  have n₂ : (δ₂ : ℂ) ≠ 0 := by rcases e₂ with h | h <;> rw [h] <;> norm_num
  have n₃ : (δ₃ : ℂ) ≠ 0 := by rcases e₃ with h | h <;> rw [h] <;> norm_num
  have m₀ : (f₀ : ℂ) ≠ 0 := by exact_mod_cast hf₀
  have m₁ : (f₁ : ℂ) ≠ 0 := by exact_mod_cast hf₁
  have m₂ : (f₂ : ℂ) ≠ 0 := by exact_mod_cast hf₂
  have m₃ : (f₃ : ℂ) ≠ 0 := by exact_mod_cast hf₃
  have key : ((q : ℂ) ^ 2 / (δ₀ * f₀) + 1 / (δ₁ * f₁) + (2 + ε * q) ^ 2 / (δ₂ * f₂) +
      (1 + 2 * ε * q) ^ 2 / (δ₃ * f₃) - (q : ℂ) ^ 2 / (δ₂ * f₂) - (q : ℂ) ^ 2 / (δ₂ * f₂) -
      1 / (δ₃ * f₃) - 1 / (δ₃ * f₃)) * ((δ₀ * f₀) * (δ₁ * f₁) * (δ₂ * f₂) * (δ₃ * f₃)) =
      (q : ℂ) ^ 2 * (δ₁ * f₁) * (δ₂ * f₂) * (δ₃ * f₃) + (δ₀ * f₀) * (δ₂ * f₂) * (δ₃ * f₃) +
        ((2 + ε * q) ^ 2 - 2 * q ^ 2) * (δ₀ * f₀) * (δ₁ * f₁) * (δ₃ * f₃) +
        ((1 + 2 * ε * q) ^ 2 - 2) * (δ₀ * f₀) * (δ₁ * f₁) * (δ₂ * f₂) := by
    field_simp
    ring
  rw [h, zero_mul] at key
  have hC : ((-(δ₀ * f₀ * (δ₂ * f₂) * -(δ₃ * f₃)) - q ^ 2 * (δ₁ * f₁) * (δ₂ * f₂) * -(δ₃ * f₃) +
      (2 * q ^ 2 - (2 + ε * q) ^ 2) * (δ₁ * f₁) * (δ₀ * f₀) * -(δ₃ * f₃) +
      ((1 + 2 * ε * q) ^ 2 - 2) * (δ₁ * f₁) * (δ₀ * f₀) * (δ₂ * f₂) : ℤ) : ℂ) = 0 := by
    push_cast
    linear_combination -key
  exact_mod_cast hC

end CFSG.Wreathed.FlatRelative
