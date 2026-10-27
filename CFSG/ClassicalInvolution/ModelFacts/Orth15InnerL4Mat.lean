module

public import CFSG.ClassicalInvolution.SmallOrth.PlusFourMain
public import CFSG.Foundations.Basic

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem ringChar_ne_two (h2 : (2 : F) ≠ 0) : ringChar F ≠ 2 := by
  intro h
  have h3 : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).mpr (by rw [h])
  exact h2 (by simpa using h3)

theorem exists_sq_add_sq [Finite F] (h2 : (2 : F) ≠ 0) (b : F) : ∃ x y : F, x * x + y * y = b := by
  have := Fintype.ofFinite F
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two (ringChar_ne_two h2)
  have hf : (Polynomial.X ^ 2 : Polynomial F).degree = 2 := by
    rw [Polynomial.degree_X_pow]
    rfl
  have hg : (Polynomial.X ^ 2 - Polynomial.C b : Polynomial F).degree = 2 := by
    rw [Polynomial.degree_sub_C (by rw [Polynomial.degree_X_pow]; exact_mod_cast two_pos)]
    rw [Polynomial.degree_X_pow]
    rfl
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  refine ⟨x, y, ?_⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C] at h
  linear_combination h

@[expose] def r0 : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem coe_r0 : ((r0 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem exists_vec [Finite F] (h2 : (2 : F) ≠ 0) {a b c : F} (habc : a * a + b * c = -1) :
    ∃ v₁ v₂ : F, b * v₂ * v₂ + 2 * a * v₁ * v₂ - c * v₁ * v₁ = 1 := by
  by_cases hb : b = 0
  · have ha : a ≠ 0 := by
      rintro rfl
      rw [hb] at habc
      simp at habc
    refine ⟨1, (1 + c) / (2 * a), ?_⟩
    rw [hb]
    field_simp
    ring
  · obtain ⟨x, y, hxy⟩ := exists_sq_add_sq h2 b
    refine ⟨y, (x - a * y) / b, ?_⟩
    field_simp
    linear_combination (y * y) * (-habc) + hxy

theorem exists_conj_r0 [Finite F] (h2 : (2 : F) ≠ 0) (r : SL(2, F))
    (hr : (r : Matrix (Fin 2) (Fin 2) F) * r = -1) : ∃ h : SL(2, F), h * r0 * h⁻¹ = r := by
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : F, (r : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have := r.2
    rw [hM, Matrix.det_fin_two_of] at this
    exact this
  rw [hM] at hr
  have e00 := congrFun (congrFun hr 0) 0
  have e01 := congrFun (congrFun hr 0) 1
  have e10 := congrFun (congrFun hr 1) 0
  have e11 := congrFun (congrFun hr 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hda : d = -a := by
    by_contra hne
    have hs : a + d ≠ 0 := fun h => hne (by linear_combination h)
    have hb0 : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc0 : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    apply hs
    rw [hb0, hc0] at hdet e00 e11
    have h1 : a * a = -1 := by linear_combination e00
    have h2' : d * d = -1 := by linear_combination e11
    have h3 : a * d = 1 := by linear_combination hdet
    have h4 : (a + d) * (a + d) = 0 := by linear_combination h1 + h2' + 2 * h3
    exact mul_self_eq_zero.mp h4
  have habc : a * a + b * c = -1 := by linear_combination e00
  obtain ⟨v₁, v₂, hv⟩ := exists_vec h2 habc
  have hdh : (!![v₁, -(a * v₁ + b * v₂); v₂, -(c * v₁ - a * v₂)] : Matrix (Fin 2) (Fin 2) F).det
      = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hv
  let h : SL(2, F) := ⟨!![v₁, -(a * v₁ + b * v₂); v₂, -(c * v₁ - a * v₂)], hdh⟩
  refine ⟨h, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hM]
  show !![v₁, -(a * v₁ + b * v₂); v₂, -(c * v₁ - a * v₂)] * !![0, 1; -1, 0] =
    !![a, b; c, d] * !![v₁, -(a * v₁ + b * v₂); v₂, -(c * v₁ - a * v₂)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hda] <;> ring_nf <;>
    first | ring1 | linear_combination v₁ * habc | linear_combination v₂ * habc

theorem isQuasisimple_sl2 [Finite F] (h4 : 4 ≤ Nat.card F) : CFSG.IsQuasisimple SL(2, F) := by
  obtain ⟨hperf, hsimple⟩ :=
    CFSG.ClassicalGroups.Orthogonal.Small.isQuasisimple_specialLinearGroup_two (K := F) h4
  have hP : Group.IsPerfect SL(2, F) := Group.isPerfect_def.mpr hperf
  refine ⟨hP, hsimple, ?_⟩
  by_contra h
  push Not at h
  have h1 : IsMulCommutative (SL(2, F) ⧸ Subgroup.center SL(2, F)) := ⟨⟨h⟩⟩
  have h2 : Group.IsPerfect (SL(2, F) ⧸ Subgroup.center SL(2, F)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center SL(2, F)))
      (QuotientGroup.mk'_surjective _)
  have h3 : Nontrivial (SL(2, F) ⧸ Subgroup.center SL(2, F)) := hsimple.toNontrivial
  exact Group.IsPerfect.not_isMulCommutative (SL(2, F) ⧸ Subgroup.center SL(2, F)) h1

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
