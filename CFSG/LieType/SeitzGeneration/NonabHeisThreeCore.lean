module

public import CFSG.LieType.SeitzGeneration.NonabHeisThreeTrans
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F]

@[expose] def circSL (a b d : F) (h : a ^ 3 + b ^ 3 + d ^ 3 - 3 * a * b * d = 1) :
    SpecialLinearGroup (Fin 3) F :=
  ⟨!![a, d, b; b, a, d; d, b, a], by rw [Matrix.det_fin_three]; simp; linear_combination h⟩

theorem circSL_mul_shiftSL (a b d : F) (h : a ^ 3 + b ^ 3 + d ^ 3 - 3 * a * b * d = 1) :
    circSL a b d h * shiftSL = shiftSL * circSL a b d h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [circSL, shiftSL, Matrix.mul_apply, Fin.sum_univ_three]

theorem shiftSL_eq_circSL : (shiftSL : SpecialLinearGroup (Fin 3) F) =
    circSL 0 1 0 (by norm_num) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [circSL, shiftSL]

theorem odd_transvection {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K)
    (hcirc : ∀ (a b d : F) (h : a ^ 3 + b ^ 3 + d ^ 3 - 3 * a * b * d = 1), circSL a b d h ∈ K)
    {c : F} (hc : c ^ 2 + c + 1 = 0) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∃ (T : SpecialLinearGroup (Fin 3) F) (u φ : Fin 3 → F),
      (T : Matrix (Fin 3) (Fin 3) F) = 1 + Matrix.vecMulVec u φ ∧ u 2 = 0 ∧ u 0 ≠ 0 ∧
        u 1 ≠ 0 ∧ φ 2 ≠ 0 ∧ T ∈ K := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hd : (-c) * (-c ^ 2) * 1 = 1 := by linear_combination (c - 1) * hc
  have hs : (-1 / 2 : F) ^ 3 + (-(c + 2) / 2) ^ 3 + ((c - 1) / 2) ^ 3 -
      3 * (-1 / 2) * (-(c + 2) / 2) * ((c - 1) / 2) = 1 := by
    field_simp
    linear_combination (-12) * hc
  have hx : diagSL (-c) (-c ^ 2) 1 hd * circSL (-1 / 2) (-(c + 2) / 2) ((c - 1) / 2) hs ∈ K :=
    K.mul_mem (hdiag _ _ _ _) (hcirc _ _ _ _)
  refine ⟨(diagSL (-c) (-c ^ 2) 1 hd * circSL (-1 / 2) (-(c + 2) / 2) ((c - 1) / 2) hs) *
    (diagSL (-c) (-c ^ 2) 1 hd * circSL (-1 / 2) (-(c + 2) / 2) ((c - 1) / 2) hs),
    ![1, c, 0], ![-(1 + 2 * c) / 2, (1 - c) / 2, -3 * c / 2], ?_, by simp, by simp,
    by simpa using hc0, div_ne_zero (mul_ne_zero (neg_ne_zero.2 h3) hc0) h2, K.mul_mem hx hx⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, circSL, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp
  case «0».«0» => linear_combination (-2 + 4 * c - c ^ 3) * hc
  case «0».«1» => linear_combination (-2 - c ^ 2) * hc
  case «0».«2» => linear_combination (4 - 3 * c + c ^ 2) * hc
  case «1».«0» => linear_combination (2 + c + c ^ 2) * hc
  case «1».«1» => linear_combination (-4 + 2 * c + 2 * c ^ 2 - c ^ 3) * hc
  case «1».«2» => linear_combination (5 : F) * hc
  case «2».«0» => linear_combination (1 - 3 * c - c ^ 2) * hc
  case «2».«1» => linear_combination (2 - 2 * c) * hc
  case «2».«2» => linear_combination (-3 + c + c ^ 2) * hc

theorem char2_transvection {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K)
    (hcirc : ∀ (a b d : F) (h : a ^ 3 + b ^ 3 + d ^ 3 - 3 * a * b * d = 1), circSL a b d h ∈ K)
    {s : F} (h2 : (2 : F) = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hM : s ^ 2 + s + 1 ≠ 0) :
    ∃ (T : SpecialLinearGroup (Fin 3) F) (u φ : Fin 3 → F),
      (T : Matrix (Fin 3) (Fin 3) F) = 1 + Matrix.vecMulVec u φ ∧ u 2 = 0 ∧ u 0 ≠ 0 ∧
        u 1 ≠ 0 ∧ φ 2 ≠ 0 ∧ T ∈ K := by
  have ha : 1 + s ≠ 0 := by
    intro h; apply hs1; linear_combination h - h2
  have ha' : s + 1 ≠ 0 := by
    intro h; apply hs1; linear_combination h - h2
  have hM' : s * (s + 1) + 1 ≠ 0 := by
    intro h; apply hM; linear_combination h
  have hd : (1 + s) * (1 + s)⁻¹ * 1 = 1 := by field_simp
  have hdet : ((1 + s) / (s ^ 2 + s + 1)) ^ 3 + ((s ^ 2 + s) / (s ^ 2 + s + 1)) ^ 3 +
      (s / (s ^ 2 + s + 1)) ^ 3 - 3 * ((1 + s) / (s ^ 2 + s + 1)) *
        ((s ^ 2 + s) / (s ^ 2 + s + 1)) * (s / (s ^ 2 + s + 1)) = 1 := by
    field_simp
    linear_combination (-3 * s ^ 2 - 5 * s ^ 3 - 3 * s ^ 4) * h2
  have hx : circSL ((1 + s) / (s ^ 2 + s + 1)) ((s ^ 2 + s) / (s ^ 2 + s + 1))
      (s / (s ^ 2 + s + 1)) hdet * diagSL (1 + s) (1 + s)⁻¹ 1 hd ∈ K :=
    K.mul_mem (hcirc _ _ _ _) (hdiag _ _ _ _)
  refine ⟨(circSL ((1 + s) / (s ^ 2 + s + 1)) ((s ^ 2 + s) / (s ^ 2 + s + 1))
      (s / (s ^ 2 + s + 1)) hdet * diagSL (1 + s) (1 + s)⁻¹ 1 hd) *
    (circSL ((1 + s) / (s ^ 2 + s + 1)) ((s ^ 2 + s) / (s ^ 2 + s + 1))
      (s / (s ^ 2 + s + 1)) hdet * diagSL (1 + s) (1 + s)⁻¹ 1 hd),
    ![1, 1 + s, 0], ![s ^ 2 / (s ^ 2 + s + 1), s ^ 2 / ((1 + s) * (s ^ 2 + s + 1)),
      s ^ 3 / ((1 + s) * (s ^ 2 + s + 1))], ?_, by simp, by simp, by simpa using ha,
    div_ne_zero (pow_ne_zero 3 hs0) (mul_ne_zero ha hM), K.mul_mem hx hx⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, circSL, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp
  case «0».«0» => linear_combination (s + 2 * s ^ 2 + 2 * s ^ 3) * h2
  case «0».«1» => linear_combination (1 + s + s ^ 2) * h2
  case «0».«2» => linear_combination (1 + 4 * s + 4 * s ^ 2 + 2 * s ^ 3) * h2
  case «1».«0» => linear_combination (1 + 2 * s + s ^ 2) * h2
  case «1».«1» => linear_combination (-s - 2 * s ^ 2 - 2 * s ^ 3 - 2 * s ^ 4 - s ^ 5) * h2
  case «1».«2» => linear_combination (1 + s + s ^ 2 + s ^ 3) * h2
  case «2».«0» => linear_combination (s + 3 * s ^ 2 + 3 * s ^ 3 + s ^ 4) * h2
  case «2».«1» => linear_combination (s + 2 * s ^ 2 + s ^ 3) * h2
  case «2».«2» => linear_combination (0 : F) * h2

section Counting

variable [Finite F]

theorem exists_pow_three_ne_one (h : 4 < Nat.card F) : ∃ g : F, g ≠ 0 ∧ g ^ 3 ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have := Fintype.ofFinite F
  have hsub : (Finset.univ.erase (0 : F)) ⊆ Polynomial.nthRootsFinset 3 (1 : F) := by
    intro g hg
    rw [Finset.mem_erase] at hg
    rw [Polynomial.mem_nthRootsFinset (by norm_num)]
    exact hcon g hg.1
  have h1 := Finset.card_le_card hsub
  have h2 : (Polynomial.nthRootsFinset 3 (1 : F)).card ≤ 3 :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 (1 : F))
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card] at h1
  omega

theorem exists_ne_four {α : Type*} [Finite α] (h : 4 < Nat.card α) (a b c d : α) :
    ∃ s : α, s ≠ a ∧ s ≠ b ∧ s ≠ c ∧ s ≠ d := by
  classical
  by_contra hcon
  push Not at hcon
  have := Fintype.ofFinite α
  have hsub : (Finset.univ : Finset α) ⊆ {a, b, c, d} := by
    intro s _
    by_cases h1 : s = a
    · simp [h1]
    by_cases h2 : s = b
    · simp [h2]
    by_cases h3 : s = c
    · simp [h3]
    simp [hcon s h1 h2 h3]
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b, c, d} : Finset α).card ≤ 4 := Finset.card_le_four
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  omega

end Counting

theorem eq_top_of_torus_circ [Finite F] {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K)
    (hcirc : ∀ (a b d : F) (h : a ^ 3 + b ^ 3 + d ^ 3 - 3 * a * b * d = 1), circSL a b d h ∈ K)
    {c : F} (hc : c ^ 2 + c + 1 = 0) (hc1 : c ≠ 1) (hcard : 4 < Nat.card F) : K = ⊤ := by
  obtain ⟨g, hg0, hg3⟩ := exists_pow_three_ne_one hcard
  have hshift : (shiftSL : SpecialLinearGroup (Fin 3) F) ∈ K := by
    rw [shiftSL_eq_circSL]; exact hcirc _ _ _ _
  by_cases h2 : (2 : F) = 0
  · obtain ⟨s, hsa, hsb, hsc, hsd⟩ := exists_ne_four hcard 0 1 c (c ^ 2)
    have hM : s ^ 2 + s + 1 ≠ 0 := by
      have : s ^ 2 + s + 1 = (s - c) * (s - c ^ 2) := by linear_combination (s - c + 1) * hc
      rw [this]
      exact mul_ne_zero (sub_ne_zero.2 hsc) (sub_ne_zero.2 hsd)
    obtain ⟨T, u, φ, hT, hu2, hu0, hu1, hφ2, hTK⟩ := char2_transvection hdiag hcirc h2 hsa hsb hM
    exact eq_top_of_torus_shift_transvection hdiag hshift hg0 hg3 hT hu2 hu0 hu1 hφ2 hTK
  · have h3 : (3 : F) ≠ 0 := by
      intro h
      apply hc1
      have : (c - 1) ^ 2 = 0 := by linear_combination hc - c * h
      exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 this)
    obtain ⟨T, u, φ, hT, hu2, hu0, hu1, hφ2, hTK⟩ := odd_transvection hdiag hcirc hc h2 h3
    exact eq_top_of_torus_shift_transvection hdiag hshift hg0 hg3 hT hu2 hu0 hu1 hφ2 hTK

end CFSG.LieType.SeitzGeneration
