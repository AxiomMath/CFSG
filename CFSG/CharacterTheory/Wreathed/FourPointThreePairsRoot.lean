module

public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootParity
public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsSupport
public import CFSG.CharacterTheory.Wreathed.FourPointOrderEightColumns
public import CFSG.CharacterTheory.Wreathed.FourPointOrderEightSupport

public noncomputable section

namespace CFSG.Wreathed.FourPointThreePairs

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.WreathCentralSquare
  CFSG.Wreathed.SquareRootSmallCharacterRigidity CFSG.Wreathed.ConditionalSquareRoot
  CFSG.Wreathed.FourPointGaussianColumns CFSG.Wreathed.FourPointOrderEight

open scoped BigOperators Classical

theorem eq_re_add_imCoeff_mul {i : ℂ} (hi : i ^ 2 = -1) (t : ℂ) :
    t = (t.re : ℂ) + (imCoeff i t : ℂ) * i := by
  obtain ⟨h0, -⟩ := re_eq_zero_and_im_sq_eq_one hi
  have hne := im_ne_zero hi
  apply Complex.ext
  · simp [h0]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, h0,
      mul_zero, zero_add, add_zero, imCoeff]
    field_simp

theorem conj_eq_neg_of_sq_eq_neg_one {i : ℂ} (hi : i ^ 2 = -1) : starRingEnd ℂ i = -i := by
  obtain ⟨h0, -⟩ := re_eq_zero_and_im_sq_eq_one hi
  apply Complex.ext <;> simp [h0]

theorem imCoeff_add_two_mul_div_three (i T U : ℂ) :
    imCoeff i ((T + 2 * U) / 3) = (imCoeff i T + 2 * imCoeff i U) / 3 := by
  unfold imCoeff
  have h3 : ((T + 2 * U) / 3).im = (T.im + 2 * U.im) / 3 := by
    rw [Complex.div_ofNat_im, Complex.add_im, Complex.mul_im]
    simp
  rw [h3]
  ring

theorem fourier_one_sub_three {i : ℂ} (hi : i ^ 2 = -1) (v : ℕ → Fin 2 → ℂ) (α β : ℂ)
    (h1 : v 1 0 = α) (h2 : v 2 0 = β) (h3 : v 3 0 = starRingEnd ℂ α) :
    (1 / 4) * ∑ n' ∈ Finset.Icc 1 3, (i ^ (1 * n') - 1) * v n' 0 -
      (1 / 4) * ∑ n' ∈ Finset.Icc 1 3, (i ^ (3 * n') - 1) * v n' 0 = -(imCoeff i α : ℂ) := by
  have hα := eq_re_add_imCoeff_mul hi α
  have hconj : starRingEnd ℂ α = (α.re : ℂ) - (imCoeff i α : ℂ) * i := by
    conv_lhs => rw [hα]
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, conj_eq_neg_of_sq_eq_neg_one hi]
    ring
  have hi3 : i ^ 3 = -i := by
    rw [pow_succ, hi]
    ring
  have hi6 : i ^ 6 = -1 := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, hi]
    norm_num
  have hi9 : i ^ 9 = i := by
    rw [show (9 : ℕ) = 2 * 4 + 1 by rfl, pow_succ, pow_mul, hi]
    norm_num
  rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) from rfl, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, h1, h2, h3, hconj]
  simp only [Nat.reduceMul, pow_one, hi, hi3, hi6, hi9]
  linear_combination (i / 2) * hα + (imCoeff i α : ℂ) * hi

theorem fourier_rows_at_one (i : ℂ) (v : ℕ → Fin 2 → ℂ) (c : ℕ → ℂ)
    (h1 : v 1 0 + 2 * v 1 1 = c 1) (h2 : v 2 0 + 2 * v 2 1 = c 2)
    (h3 : v 3 0 + 2 * v 3 1 = c 3) (j : ℕ) :
    (1 / 4) * ∑ n' ∈ Finset.Icc 1 3, (i ^ (j * n') - 1) * v n' 0 +
      2 * ((1 / 4) * ∑ n' ∈ Finset.Icc 1 3, (i ^ (j * n') - 1) * v n' 1) =
    (4 : ℂ)⁻¹ * ∑ k ∈ Finset.range 4, (i ^ (j * k) - 1) * c k := by
  rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) from rfl, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, ← h1, ← h2, ← h3]
  simp only [mul_zero, pow_zero, sub_self, zero_mul, zero_add]
  ring

theorem root_eigen_facts {G : Type} [Group G] (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ 2))
    (data : FiniteComplexRepresentation G) {i η : ℂ} (hi : i ^ 2 = -1) (hη : η ^ 2 = i) :
    let ν : ℕ → ℕ := fun t => cyclicEigenmultiplicity data (actualRoot S e) η t
    ν 1 = ν 5 ∧ ν 3 = ν 7 ∧
    data.character (actualRoot S e) =
      (((ν 0 : ℤ) - ν 4 : ℤ) : ℂ) + (((ν 2 : ℤ) - ν 6 : ℤ) : ℂ) * i ∧
    data.character (actualRoot S e ^ 2) =
      (((ν 0 : ℤ) + ν 4 - ν 2 - ν 6 : ℤ) : ℂ) + ((2 * ((ν 1 : ℤ) - ν 3) : ℤ) : ℂ) * i ∧
    (Module.finrank ℂ data.vector : ℤ) = ∑ t ∈ Finset.range 8, (ν t : ℤ) ∧
    ∀ j : ℕ, 1 ≤ j → j < 4 →
      (4 : ℂ)⁻¹ * ∑ k ∈ Finset.range 4,
          (i ^ (j * k) - 1) * data.character (actualRoot S e ^ (2 * k)) =
        (((ν (4 - j) : ℤ) + ν (8 - j) - ν 0 - ν 4 : ℤ) : ℂ) := by
  intro ν
  have hη8 : IsPrimitiveRoot η (2 * 2 ^ 2) := isPrimitiveRoot_eight_of_sq_eq hi hη
  have hy : actualRoot S e ^ (2 * 2 ^ 2) = 1 := by
    rw [← actualRoot_orderOf 2 le_rfl S e]
    exact pow_orderOf_eq_one _
  have h15 : ν 1 = ν 5 :=
    actual_root_odd_eigenmultiplicity_cancellation 2 le_rfl S e data η hη8 1 odd_one
  have h37 : ν 3 = ν 7 :=
    actual_root_odd_eigenmultiplicity_cancellation 2 le_rfl S e data η hη8 3 ⟨1, rfl⟩
  have hexp : ∀ h : ℕ, data.character (actualRoot S e ^ h) =
      ∑ t ∈ Finset.range 8, (ν t : ℂ) * η ^ (t * h) :=
    character_cyclic_eigenmultiplicity_expansion data _ (2 * 2 ^ 2) (by norm_num) hy η hη8
  have h4 : η ^ 4 = -1 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hη, hi]
  have h3 : η ^ 3 = η * i := by
    rw [pow_succ, hη]
    ring
  have h5 : η ^ 5 = -η := by
    rw [pow_succ, h4]
    ring
  have h6 : η ^ 6 = -i := by
    rw [show (6 : ℕ) = 4 + 2 by rfl, pow_add, h4, hη]
    ring
  have h7 : η ^ 7 = -(η * i) := by
    rw [pow_succ, h6]
    ring
  have h8 : η ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 * 2 by rfl, pow_mul, h4]
    norm_num
  have h10 : η ^ 10 = i := by
    rw [show (10 : ℕ) = 8 + 2 by rfl, pow_add, h8, hη, one_mul]
  have h12 : η ^ 12 = -1 := by
    rw [show (12 : ℕ) = 8 + 4 by rfl, pow_add, h8, h4, one_mul]
  have h14 : η ^ 14 = -i := by
    rw [show (14 : ℕ) = 8 + 6 by rfl, pow_add, h8, h6, one_mul]
  refine ⟨h15, h37, ?_, ?_, ?_, ?_⟩
  · have h := hexp 1
    rw [pow_one] at h
    rw [h]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_one, pow_zero,
      pow_one, hη, h3, h4, h5, h6, h7]
    rw [← h15, ← h37]
    push_cast
    ring
  · rw [hexp 2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceMul, pow_zero,
      hη, h4, h6, h8, h10, h12, h14]
    rw [← h15, ← h37]
    push_cast
    ring
  · have h := character_cyclic_eigenmultiplicity_degree data (actualRoot S e) (2 * 2 ^ 2)
      (by norm_num) hy η hη8
    rw [← h]
    push_cast
    rfl
  · intro j hj1 hj4
    have h := fourier_character_square_powers data (actualRoot S e) (m := 4) (by norm_num) hy hη8
      hj1 hj4
    rw [hη, Nat.cast_ofNat] at h
    exact h

end CFSG.Wreathed.FourPointThreePairs
