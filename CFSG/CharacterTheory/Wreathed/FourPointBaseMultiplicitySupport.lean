module

public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsSupport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FourPointBaseMultiplicity

section Powers

variable {i : ℂ} (hi : i ^ 2 = -1)
include hi

theorem conj_eq_neg : conj i = -i := by
  have h0 := (FourPointGaussianColumns.re_eq_zero_and_im_sq_eq_one hi).1
  apply Complex.ext <;> simp [h0]

theorem inv_eq_neg : i⁻¹ = -i := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [mul_neg, ← sq, hi, neg_neg]

theorem inverse_one (F : ℕ → ℂ) :
    ∑ j ∈ Finset.Icc 1 3, F j * i ^ (-((j : ℤ) * ((1 : ℕ) : ℤ))) = -F 2 + i * (F 3 - F 1) := by
  have h3 : i ^ 3 = -i := by rw [pow_succ, hi, neg_one_mul]
  have hz : ∀ j k : ℕ, i ^ (-((j : ℤ) * (k : ℤ))) = (i ^ (j * k))⁻¹ := fun j k => by
    rw [← Nat.cast_mul, zpow_neg, zpow_natCast]
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [hz, Nat.reduceMul, pow_one, hi, h3, inv_eq_neg hi, inv_neg, inv_one]
  ring

theorem inverse_two (F : ℕ → ℂ) :
    ∑ j ∈ Finset.Icc 1 3, F j * i ^ (-((j : ℤ) * ((2 : ℕ) : ℤ))) = -F 1 + F 2 - F 3 := by
  have h4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hi]; norm_num
  have h6 : i ^ 6 = -1 := by rw [show (6 : ℕ) = 4 + 2 by norm_num, pow_add, h4, hi, one_mul]
  have hz : ∀ j k : ℕ, i ^ (-((j : ℤ) * (k : ℤ))) = (i ^ (j * k))⁻¹ := fun j k => by
    rw [← Nat.cast_mul, zpow_neg, zpow_natCast]
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [hz, Nat.reduceMul, hi, h4, h6, inv_neg, inv_one]
  ring

theorem inverse_three (F : ℕ → ℂ) :
    ∑ j ∈ Finset.Icc 1 3, F j * i ^ (-((j : ℤ) * ((3 : ℕ) : ℤ))) = -F 2 - i * (F 3 - F 1) := by
  have h3 : i ^ 3 = -i := by rw [pow_succ, hi, neg_one_mul]
  have h4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hi]; norm_num
  have h6 : i ^ 6 = -1 := by rw [show (6 : ℕ) = 4 + 2 by norm_num, pow_add, h4, hi, one_mul]
  have h9 : i ^ 9 = i := by
    rw [show (9 : ℕ) = 4 + 4 + 1 by norm_num, pow_add, pow_add, h4, pow_one, one_mul, one_mul]
  have hz : ∀ j k : ℕ, i ^ (-((j : ℤ) * (k : ℤ))) = (i ^ (j * k))⁻¹ := fun j k => by
    rw [← Nat.cast_mul, zpow_neg, zpow_natCast]
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [hz, Nat.reduceMul, h3, h6, h9, inv_eq_neg hi, inv_neg, inv_one, neg_neg]
  ring

end Powers

theorem sum_comb_mul_conj {ι : Type*} (B : Finset ι) (g₁ g₂ g₃ : ι → ℂ)
    (h₁ : ∀ χ ∈ B, conj (g₁ χ) = g₁ χ) (h₂ : ∀ χ ∈ B, conj (g₂ χ) = g₂ χ)
    (h₃ : ∀ χ ∈ B, conj (g₃ χ) = g₃ χ) (a₁ a₂ a₃ b₁ b₂ b₃ : ℂ) :
    ∑ χ ∈ B, (a₁ * g₁ χ + a₂ * g₂ χ + a₃ * g₃ χ) * conj (b₁ * g₁ χ + b₂ * g₂ χ + b₃ * g₃ χ) =
      a₁ * conj b₁ * ∑ χ ∈ B, g₁ χ * g₁ χ + a₁ * conj b₂ * ∑ χ ∈ B, g₁ χ * g₂ χ +
        a₁ * conj b₃ * ∑ χ ∈ B, g₁ χ * g₃ χ + a₂ * conj b₁ * ∑ χ ∈ B, g₂ χ * g₁ χ +
        a₂ * conj b₂ * ∑ χ ∈ B, g₂ χ * g₂ χ + a₂ * conj b₃ * ∑ χ ∈ B, g₂ χ * g₃ χ +
        a₃ * conj b₁ * ∑ χ ∈ B, g₃ χ * g₁ χ + a₃ * conj b₂ * ∑ χ ∈ B, g₃ χ * g₂ χ +
        a₃ * conj b₃ * ∑ χ ∈ B, g₃ χ * g₃ χ := by
  have hpt : ∀ χ ∈ B, (a₁ * g₁ χ + a₂ * g₂ χ + a₃ * g₃ χ) *
      conj (b₁ * g₁ χ + b₂ * g₂ χ + b₃ * g₃ χ) =
        a₁ * conj b₁ * (g₁ χ * g₁ χ) + a₁ * conj b₂ * (g₁ χ * g₂ χ) +
        a₁ * conj b₃ * (g₁ χ * g₃ χ) + a₂ * conj b₁ * (g₂ χ * g₁ χ) +
        a₂ * conj b₂ * (g₂ χ * g₂ χ) + a₂ * conj b₃ * (g₂ χ * g₃ χ) +
        a₃ * conj b₁ * (g₃ χ * g₁ χ) + a₃ * conj b₂ * (g₃ χ * g₂ χ) +
        a₃ * conj b₃ * (g₃ χ * g₃ χ) := by
    intro χ hχ
    rw [map_add, map_add, map_mul, map_mul, map_mul, h₁ χ hχ, h₂ χ hχ, h₃ χ hχ]
    ring
  rw [Finset.sum_congr rfl hpt]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem rows_gram {ι : Type*} (B : Finset ι) {i : ℂ} (hi : i ^ 2 = -1) (g : ℕ → ι → ℂ)
    (hreal : ∀ j ∈ Finset.Icc 1 3, ∀ χ ∈ B, conj (g j χ) = g j χ)
    (hgram : ∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3,
      ∑ χ ∈ B, g j χ * g k χ = 8 * ((if j = k then 1 else 0) + 1))
    (Z : ι → ℕ → ℂ)
    (hZ1 : ∀ χ ∈ B, Z χ 1 = -i * g 1 χ + -1 * g 2 χ + i * g 3 χ)
    (hZ2 : ∀ χ ∈ B, Z χ 2 = -1 * g 1 χ + 1 * g 2 χ + -1 * g 3 χ)
    (hZ3 : ∀ χ ∈ B, Z χ 3 = i * g 1 χ + -1 * g 2 χ + -i * g 3 χ) :
    ∀ k ∈ Finset.Ico 1 4, ∀ l ∈ Finset.Ico 1 4,
      ∑ χ ∈ B, Z χ k * conj (Z χ l) = if k = l then 2 * ((4 : ℕ) : ℂ) ^ 2 else 0 := by
  have hc := conj_eq_neg hi
  have G : ∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3, j ≠ k →
      ∑ χ ∈ B, g j χ * g k χ = 8 := fun j hj k hk hjk => by
    rw [hgram j hj k hk, ite_eq_right hjk]
    ring
  have G' : ∀ j ∈ Finset.Icc 1 3, ∑ χ ∈ B, g j χ * g j χ = 16 := fun j hj => by
    rw [hgram j hj j hj, ite_eq_left rfl]
    ring
  have m1 : (1 : ℕ) ∈ Finset.Icc 1 3 := by decide
  have m2 : (2 : ℕ) ∈ Finset.Icc 1 3 := by decide
  have m3 : (3 : ℕ) ∈ Finset.Icc 1 3 := by decide
  have g11 := G' 1 m1
  have g22 := G' 2 m2
  have g33 := G' 3 m3
  have g12 := G 1 m1 2 m2 (by decide)
  have g13 := G 1 m1 3 m3 (by decide)
  have g21 := G 2 m2 1 m1 (by decide)
  have g23 := G 2 m2 3 m3 (by decide)
  have g31 := G 3 m3 1 m1 (by decide)
  have g32 := G 3 m3 2 m2 (by decide)
  have key := fun a₁ a₂ a₃ b₁ b₂ b₃ => sum_comb_mul_conj B (g 1) (g 2) (g 3) (hreal 1 m1)
    (hreal 2 m2) (hreal 3 m3) a₁ a₂ a₃ b₁ b₂ b₃
  intro k hk l hl
  rw [Finset.mem_Ico] at hk hl
  obtain ⟨hk1, hk4⟩ := hk
  obtain ⟨hl1, hl4⟩ := hl
  interval_cases k <;> interval_cases l
  · rw [Finset.sum_congr rfl fun χ hχ => by rw [hZ1 χ hχ], key, g11, g12, g13, g21, g22, g23,
      g31, g32, g33]
    simp only [map_neg, map_one, hc, ↓reduceIte]
    linear_combination (-16 : ℂ) * hi
  · rw [Finset.sum_congr rfl fun χ hχ => by rw [hZ1 χ hχ, hZ2 χ hχ],
      key, g11, g12, g13, g21, g22, g23, g31, g32, g33]
    simp only [map_neg, map_one, Nat.reduceEqDiff, ↓reduceIte]
    linear_combination (0 : ℂ) * hi
  · rw [Finset.sum_congr rfl fun χ hχ => by rw [hZ1 χ hχ, hZ3 χ hχ],
      key, g11, g12, g13, g21, g22, g23, g31, g32, g33]
    simp only [map_neg, map_one, hc, Nat.reduceEqDiff, ↓reduceIte]
    linear_combination (16 : ℂ) * hi
  · rw [Finset.sum_congr rfl fun χ hχ => by rw [hZ2 χ hχ, hZ1 χ hχ],
      key, g11, g12, g13, g21, g22, g23, g31, g32, g33]
    simp only [map_neg, map_one, hc, Nat.reduceEqDiff, ↓reduceIte]
    linear_combination (0 : ℂ) * hi
  · rw [Finset.sum_congr rfl fun χ hχ => by rw [hZ2 χ hχ], key, g11, g12, g13, g21, g22, g23,
      g31, g32, g33]
    simp only [map_neg, map_one, ↓reduceIte]
    linear_combination (0 : ℂ) * hi
  · rw [Finset.sum_congr rfl fun χ hχ => by rw [hZ2 χ hχ, hZ3 χ hχ],
      key, g11, g12, g13, g21, g22, g23, g31, g32, g33]
    simp only [map_neg, map_one, hc, Nat.reduceEqDiff, ↓reduceIte]
    linear_combination (0 : ℂ) * hi
  · rw [Finset.sum_congr rfl fun χ hχ => by rw [hZ3 χ hχ, hZ1 χ hχ],
      key, g11, g12, g13, g21, g22, g23, g31, g32, g33]
    simp only [map_neg, map_one, hc, Nat.reduceEqDiff, ↓reduceIte]
    linear_combination (16 : ℂ) * hi
  · rw [Finset.sum_congr rfl fun χ hχ => by rw [hZ3 χ hχ, hZ2 χ hχ],
      key, g11, g12, g13, g21, g22, g23, g31, g32, g33]
    simp only [map_neg, map_one, Nat.reduceEqDiff, ↓reduceIte]
    linear_combination (0 : ℂ) * hi
  · rw [Finset.sum_congr rfl fun χ hχ => by rw [hZ3 χ hχ], key, g11, g12, g13, g21, g22, g23,
      g31, g32, g33]
    simp only [map_neg, map_one, hc, ↓reduceIte]
    linear_combination (-16 : ℂ) * hi

theorem base_value_formulas {i : ℂ} (hi : i ^ 2 = -1) (L₁ L₂ L₃ h₁ h₂ h₃ c₁ c₂ c₃ cs : ℤ)
    (v₁₀ v₁₁ v₂₀ v₂₁ T U A B : ℂ)
    (hv₁₀ : v₁₀ = -L₂ + i * (L₃ - L₁)) (hv₁₁ : v₁₁ = -h₂ + i * (h₃ - h₁))
    (hv₂₀ : v₂₀ = -L₁ + L₂ - L₃) (hv₂₁ : v₂₁ = -h₁ + h₂ - h₃)
    (hT : T = v₁₀ + 2 * v₁₁) (hU : U = v₁₀ - v₁₁) (hA : A = v₂₀ + 2 * v₂₁)
    (hB : B = v₂₀ - v₂₁)
    (e₁ : L₁ - 2 * h₁ = c₂ - 2 * c₁) (e₃ : L₃ - 2 * h₃ = c₂ - 2 * c₃)
    (e₂ : L₂ - 2 * h₂ = 2 * cs - c₂ - c₁ - c₃) :
    (c₁ : ℂ) - c₃ =
        ((4 * FourPointGaussianColumns.imCoeff i U - FourPointGaussianColumns.imCoeff i T) / 6 :
          ℝ) ∧
    T = -2 * (L₂ : ℂ) + 2 * cs - c₂ - c₁ - c₃ + 2 * i * (((L₃ : ℂ) - L₁) + ((c₃ : ℂ) - c₁)) ∧
    A = 2 * ((L₂ : ℂ) - L₁ - L₃) - 2 * cs + 3 * c₂ - c₁ - c₃ ∧
    B = ((L₂ : ℂ) - L₁ - L₃ - 3 * c₂ + c₁ + c₃) / 2 + cs ∧
    (U.re : ℂ) = (-(L₂ : ℂ) - 2 * cs + c₂ + c₁ + c₃) / 2 := by
  have h0 := (FourPointGaussianColumns.re_eq_zero_and_im_sq_eq_one hi).1
  have hT' : T = (((-L₂ - 2 * h₂ : ℤ) : ℝ) : ℂ) +
      (((L₃ - L₁ + 2 * (h₃ - h₁) : ℤ) : ℝ) : ℂ) * i := by
    rw [hT, hv₁₀, hv₁₁]
    push_cast
    ring
  have hU' : U = (((-L₂ + h₂ : ℤ) : ℝ) : ℂ) + (((L₃ - L₁ - (h₃ - h₁) : ℤ) : ℝ) : ℂ) * i := by
    rw [hU, hv₁₀, hv₁₁]
    push_cast
    ring
  have e₁' : (L₁ : ℂ) - 2 * h₁ = c₂ - 2 * c₁ := by exact_mod_cast e₁
  have e₃' : (L₃ : ℂ) - 2 * h₃ = c₂ - 2 * c₃ := by exact_mod_cast e₃
  have e₂' : (L₂ : ℂ) - 2 * h₂ = 2 * cs - c₂ - c₁ - c₃ := by exact_mod_cast e₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hT', hU', FourPointGaussianColumns.imCoeff_add_mul hi,
      FourPointGaussianColumns.imCoeff_add_mul hi]
    have h6 : ((c₁ : ℝ) - c₃) =
        (4 * ((L₃ - L₁ - (h₃ - h₁) : ℤ) : ℝ) - ((L₃ - L₁ + 2 * (h₃ - h₁) : ℤ) : ℝ)) / 6 := by
      have e₁r : (L₁ : ℝ) - 2 * h₁ = c₂ - 2 * c₁ := by exact_mod_cast e₁
      have e₃r : (L₃ : ℝ) - 2 * h₃ = c₂ - 2 * c₃ := by exact_mod_cast e₃
      push_cast
      linarith
    rw [← h6]
    push_cast
    ring
  · rw [hT, hv₁₀, hv₁₁]
    linear_combination e₂' + i * e₁' - i * e₃'
  · rw [hA, hv₂₀, hv₂₁]
    linear_combination e₁' - e₂' + e₃'
  · rw [hB, hv₂₀, hv₂₁]
    linear_combination (-1 / 2 : ℂ) * e₁' + (1 / 2 : ℂ) * e₂' - (1 / 2 : ℂ) * e₃'
  · rw [hU']
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, h0,
      mul_zero, zero_mul, sub_zero, add_zero]
    push_cast
    linear_combination (-1 / 2 : ℂ) * e₂'

end CFSG.Wreathed.FourPointBaseMultiplicity
