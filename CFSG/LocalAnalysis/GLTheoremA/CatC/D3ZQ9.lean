module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL2

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


set_option linter.unusedSectionVars false

section Matrix2

variable {K : Type} [Field K]

@[expose] def gm (b : K) (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  !![b * A 0 0, b * A 0 1; A 1 0, A 1 1]

theorem gm_det (b : K) (A : Matrix (Fin 2) (Fin 2) K) : (gm b A).det = b * A.det := by
  simp [gm, Matrix.det_fin_two]; ring

theorem conj_mul_gm (b : Kˣ) (A X : SL2 K) :
    ((dconj b (A * X * A⁻¹) : SL2 K) : Matrix (Fin 2) (Fin 2) K) * gm (b : K) (A : Matrix (Fin 2) (Fin 2) K) =
      gm (b : K) (A : Matrix (Fin 2) (Fin 2) K) * (X : Matrix (Fin 2) (Fin 2) K) := by
  have hdetA := det_SL2 A
  have hb : (b : K) ≠ 0 := b.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dconj, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, gm, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp
  · linear_combination ((A : Matrix (Fin 2) (Fin 2) K) 0 0 * (X : Matrix (Fin 2) (Fin 2) K) 0 0 +
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (X : Matrix (Fin 2) (Fin 2) K) 1 0) * hdetA
  · linear_combination ((A : Matrix (Fin 2) (Fin 2) K) 0 0 * (X : Matrix (Fin 2) (Fin 2) K) 0 1 +
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (X : Matrix (Fin 2) (Fin 2) K) 1 1) * hdetA
  · linear_combination ((A : Matrix (Fin 2) (Fin 2) K) 1 0 * (X : Matrix (Fin 2) (Fin 2) K) 0 0 +
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 * (X : Matrix (Fin 2) (Fin 2) K) 1 0) * hdetA
  · linear_combination ((A : Matrix (Fin 2) (Fin 2) K) 1 0 * (X : Matrix (Fin 2) (Fin 2) K) 0 1 +
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 * (X : Matrix (Fin 2) (Fin 2) K) 1 1) * hdetA

theorem scalar_of_commute (M : Matrix (Fin 2) (Fin 2) K)
    (hu : M * (uSL (1 : K) : Matrix (Fin 2) (Fin 2) K) = (uSL (1 : K) : Matrix (Fin 2) (Fin 2) K) * M)
    (hv : M * (vSL (1 : K) : Matrix (Fin 2) (Fin 2) K) = (vSL (1 : K) : Matrix (Fin 2) (Fin 2) K) * M) :
    ∃ μ : K, M = μ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : K, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  have h1 := congrFun (congrFun hu 0) 0
  have h2 := congrFun (congrFun hu 0) 1
  have h3 := congrFun (congrFun hv 0) 0
  simp [coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two] at h1 h2 h3
  have hd : d = a := by linear_combination -h2
  refine ⟨a, ?_⟩
  subst h1; subst h3; subst hd
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem gm_sq_scalar (b : Kˣ) (A : SL2 K)
    (h : ∀ X : SL2 K, dconj b (A * dconj b (A * X * A⁻¹) * A⁻¹) = X) :
    ∃ l : K, gm (b : K) (A : Matrix (Fin 2) (Fin 2) K) * gm (b : K) (A : Matrix (Fin 2) (Fin 2) K) =
      l • (1 : Matrix (Fin 2) (Fin 2) K) := by
  set g := gm (b : K) (A : Matrix (Fin 2) (Fin 2) K) with hg
  have h1 : ∀ X : SL2 K, ((dconj b (A * X * A⁻¹) : SL2 K) : Matrix (Fin 2) (Fin 2) K) * g =
      g * (X : Matrix (Fin 2) (Fin 2) K) := fun X => conj_mul_gm b A X
  have hcomm : ∀ X : SL2 K, g * g * (X : Matrix (Fin 2) (Fin 2) K) =
      (X : Matrix (Fin 2) (Fin 2) K) * (g * g) := by
    intro X
    have e1 := h1 X
    have e2 := h1 (dconj b (A * X * A⁻¹))
    rw [h X] at e2
    calc g * g * (X : Matrix (Fin 2) (Fin 2) K) = g * (g * (X : Matrix (Fin 2) (Fin 2) K)) := by
          rw [Matrix.mul_assoc]
      _ = g * (((dconj b (A * X * A⁻¹) : SL2 K) : Matrix (Fin 2) (Fin 2) K) * g) := by rw [e1]
      _ = (g * ((dconj b (A * X * A⁻¹) : SL2 K) : Matrix (Fin 2) (Fin 2) K)) * g := by
          rw [Matrix.mul_assoc]
      _ = ((X : Matrix (Fin 2) (Fin 2) K) * g) * g := by rw [e2]
      _ = (X : Matrix (Fin 2) (Fin 2) K) * (g * g) := by rw [Matrix.mul_assoc]
  exact scalar_of_commute (g * g) (hcomm (uSL 1)) (hcomm (vSL 1))

theorem exists_dconj_neg_aux (b : Kˣ) (A : SL2 K) (Y : Matrix (Fin 2) (Fin 2) K)
    (hY : Y * gm (b : K) (A : Matrix (Fin 2) (Fin 2) K) + gm (b : K) (A : Matrix (Fin 2) (Fin 2) K) * Y = 0)
    (hdet : Y.det = -1) :
    ∃ Y₁ : SL2 K, dconj (-1) (dconj b⁻¹ Y₁ * A * Y₁⁻¹) = HSL (-1) * A := by
  have hb : (b : K) ≠ 0 := b.ne_zero
  have hCb : ((b : K))⁻¹ * (b : K) = 1 := inv_mul_cancel₀ hb
  have hY' : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = -1 := by
    rw [Matrix.det_fin_two] at hdet; exact hdet
  obtain ⟨Y₁, y00, y01, y10, y11⟩ : ∃ Y₁ : SL2 K, (Y₁ : Matrix (Fin 2) (Fin 2) K) 0 0 = -Y 0 0 ∧
      (Y₁ : Matrix (Fin 2) (Fin 2) K) 0 1 = -Y 0 1 ∧ (Y₁ : Matrix (Fin 2) (Fin 2) K) 1 0 = Y 1 0 ∧
      (Y₁ : Matrix (Fin 2) (Fin 2) K) 1 1 = Y 1 1 := by
    refine ⟨⟨!![-Y 0 0, -Y 0 1; Y 1 0, Y 1 1], ?_⟩, rfl, rfl, rfl, rfl⟩
    simp [Matrix.det_fin_two]; linear_combination -hY'
  refine ⟨Y₁, ?_⟩
  have e00 := congrFun (congrFun hY 0) 0
  have e01 := congrFun (congrFun hY 0) 1
  have e10 := congrFun (congrFun hY 1) 0
  have e11 := congrFun (congrFun hY 1) 1
  simp only [gm, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.zero_apply] at e00 e01 e10 e11
  have h1 : dconj (-1) (dconj b⁻¹ Y₁ * A) = (HSL (-1) * A) * dconj (-1) Y₁ := by
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [coe_dconj, coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, y00, y01, y10, y11]
    · linear_combination (-((b : K))⁻¹) * e00 +
        (2 * (A : Matrix (Fin 2) (Fin 2) K) 0 0 * Y 0 0 + (A : Matrix (Fin 2) (Fin 2) K) 0 1 * Y 1 0) * hCb
    · linear_combination ((b : K))⁻¹ * e01 +
        (-(Y 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 1 + (A : Matrix (Fin 2) (Fin 2) K) 0 0 * Y 0 1 +
          (A : Matrix (Fin 2) (Fin 2) K) 0 1 * Y 1 1)) * hCb
    · linear_combination (-1) * e10
    · linear_combination e11
  calc dconj (-1) (dconj b⁻¹ Y₁ * A * Y₁⁻¹)
      = dconj (-1) (dconj b⁻¹ Y₁ * A) * (dconj (-1) Y₁)⁻¹ := by rw [map_mul, map_inv]
    _ = ((HSL (-1) * A) * dconj (-1) Y₁) * (dconj (-1) Y₁)⁻¹ := by rw [h1]
    _ = HSL (-1) * A := by group


theorem exists_anticomm (hK2 : (2 : K) ≠ 0) (g : Matrix (Fin 2) (Fin 2) K) (hdet : g.det ≠ 0)
    (hsq : ∃ l : K, g * g = l • (1 : Matrix (Fin 2) (Fin 2) K))
    (hns : ¬ ∃ μ : K, g = μ • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ Y : Matrix (Fin 2) (Fin 2) K, Y.det = -1 ∧ Y * g + g * Y = 0 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : K, g = !![a, b; c, d] :=
    ⟨g 0 0, g 0 1, g 1 0, g 1 1, Matrix.eta_fin_two g⟩
  obtain ⟨l, hl⟩ := hsq
  have e01 : a * b + b * d = 0 := by
    have h := congrFun (congrFun hl 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have e10 : c * a + d * c = 0 := by
    have h := congrFun (congrFun hl 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have e00 : a * a + b * c = l := by
    have h := congrFun (congrFun hl 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have e11 : c * b + d * d = l := by
    have h := congrFun (congrFun hl 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  by_cases hs : a + d = 0
  · have hd : d = -a := by linear_combination hs
    subst hd
    by_cases hb : b = 0
    · by_cases hc : c = 0
      · subst hb; subst hc
        refine ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two], ?_⟩
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · subst hb
        refine ⟨!![1, -2 * a / c; 0, -1], by simp [Matrix.det_fin_two], ?_⟩
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
    · refine ⟨!![1, 0; -2 * a / b, -1], by simp [Matrix.det_fin_two], ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  · exfalso
    have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hs
    subst hb; subst hc
    have had : a = d := by
      have h2 : (a - d) * (a + d) = 0 := by linear_combination e00 - e11
      have := (mul_eq_zero.1 h2).resolve_right hs
      linear_combination this
    exact hns ⟨a, by
      subst had
      ext i j; fin_cases i <;> fin_cases j <;> simp⟩

theorem exists_dconj_neg (hK2 : (2 : K) ≠ 0) (b : Kˣ) (A : SL2 K)
    (hsq : ∃ l : K, gm (b : K) (A : Matrix (Fin 2) (Fin 2) K) * gm (b : K) (A : Matrix (Fin 2) (Fin 2) K) =
      l • (1 : Matrix (Fin 2) (Fin 2) K))
    (hns : ¬ ∃ μ : K, gm (b : K) (A : Matrix (Fin 2) (Fin 2) K) = μ • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ Y₁ : SL2 K, dconj (-1) (dconj b⁻¹ Y₁ * A * Y₁⁻¹) = HSL (-1) * A := by
  have hdet : (gm (b : K) (A : Matrix (Fin 2) (Fin 2) K)).det ≠ 0 := by
    rw [gm_det, A.2, mul_one]; exact b.ne_zero
  obtain ⟨Y, hYdet, hY⟩ := exists_anticomm hK2 _ hdet hsq hns
  exact exists_dconj_neg_aux b A Y hY hYdet

theorem eq_HSL_of_gm_scalar (b : Kˣ) (A : SL2 K) (μ : K)
    (h : gm (b : K) (A : Matrix (Fin 2) (Fin 2) K) = μ • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ u : Kˣ, A = HSL u ∧ ((u : Kˣ) : K) ^ 2 * (b : K) = 1 := by
  have hb : (b : K) ≠ 0 := b.ne_zero
  have hdetA := det_SL2 A
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [gm] at e00 e01 e10 e11
  have hμ : μ ≠ 0 := by
    intro hμ0
    rw [hμ0] at e00 e11
    have h0 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 := by
      rcases mul_eq_zero.1 e00 with h1 | h1
      · exact absurd h1 hb
      · exact h1
    rw [h0, e01, e10, e11] at hdetA
    simp at hdetA
  have hA00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = μ / b := by
    field_simp; linear_combination e00
  have hμb : μ * μ = b := by
    rw [hA00, e01, e10, e11] at hdetA
    field_simp at hdetA
    linear_combination hdetA
  refine ⟨Units.mk0 μ⁻¹ (inv_ne_zero hμ), ?_, ?_⟩
  · refine SL2_ext ?_ ?_ ?_ ?_
    · rw [hA00, coe_HSL]; simp; field_simp; linear_combination hμb
    · rw [e01, coe_HSL]; simp
    · rw [e10, coe_HSL]; simp
    · rw [e11, coe_HSL]; simp
  · simp; field_simp; linear_combination -hμb

end Matrix2

end CFSG.LocalAnalysis.GLTheoremA
