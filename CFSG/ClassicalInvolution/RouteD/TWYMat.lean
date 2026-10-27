module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open Matrix

variable {F : Type} [Field F]

theorem mat_exists_ne_zero {M : Matrix (Fin 2) (Fin 2) F} (h : M ≠ 0) : ∃ a k, M a k ≠ 0 := by
  by_contra hno
  push Not at hno
  exact h (by ext a k; exact hno a k)

theorem mat_exists_isotropic (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1)
    {A B : Matrix (Fin 2) (Fin 2) F} (hA : A * A = -1) (hAd : A.det = 1) (hB : B * B = -1)
    (hBd : B.det = 1) :
    ∃ X : Matrix (Fin 2) (Fin 2) F, X ≠ 0 ∧ X.det = 0 ∧ A * X * B = -X := by
  set P : Matrix (Fin 2) (Fin 2) F := A + i • 1 with hP
  set Q : Matrix (Fin 2) (Fin 2) F := B + i • 1 with hQ
  have hAP : A * P = i • P := by
    rw [hP, mul_add, hA, mul_smul_comm, mul_one, smul_add, smul_smul, hi, neg_smul, one_smul]
    abel
  have hQB : Q * B = i • Q := by
    rw [hQ, add_mul, hB, smul_mul_assoc, one_mul, smul_add, smul_smul, hi, neg_smul, one_smul]
    abel
  have hPne : P ≠ 0 := by
    intro h0
    have hA' : A = -(i • (1 : Matrix (Fin 2) (Fin 2) F)) := by
      rw [hP] at h0
      exact eq_neg_of_add_eq_zero_left h0
    rw [hA', Matrix.det_neg, Matrix.det_smul, Matrix.det_one] at hAd
    simp only [Fintype.card_fin] at hAd
    have : (2 : F) = 0 := by linear_combination hi - hAd
    exact h2 this
  have hQne : Q ≠ 0 := by
    intro h0
    have hB' : B = -(i • (1 : Matrix (Fin 2) (Fin 2) F)) := by
      rw [hQ] at h0
      exact eq_neg_of_add_eq_zero_left h0
    rw [hB', Matrix.det_neg, Matrix.det_smul, Matrix.det_one] at hBd
    simp only [Fintype.card_fin] at hBd
    have : (2 : F) = 0 := by linear_combination hi - hBd
    exact h2 this
  obtain ⟨a, k, hak⟩ := mat_exists_ne_zero hPne
  obtain ⟨l, b, hlb⟩ := mat_exists_ne_zero hQne
  refine ⟨Matrix.vecMulVec (fun r => P r k) (fun s => Q l s), ?_, ?_, ?_⟩
  · intro h0
    have := congr_fun (congr_fun h0 a) b
    simp [Matrix.vecMulVec] at this
    tauto
  · rw [Matrix.det_fin_two]
    simp [Matrix.vecMulVec]
    ring
  · rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    have h1 : A *ᵥ (fun r => P r k) = i • (fun r => P r k) := by
      ext r
      have := congr_fun (congr_fun hAP r) k
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have h2' : (fun s => Q l s) ᵥ* B = i • (fun s => Q l s) := by
      ext s
      have := congr_fun (congr_fun hQB l) s
      simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this
    rw [h1, h2']
    ext r s
    simp [Matrix.vecMulVec]
    linear_combination (P r k * Q l s) * hi

theorem mat_isSquare_of_isotropic {A B : Matrix (Fin 2) (Fin 2) F} (hB : B * B = -1)
    {X : Matrix (Fin 2) (Fin 2) F} (hX : X ≠ 0) (hXd : X.det = 0) (hAX : A * X * B = -X) :
    IsSquare (-1 : F) := by
  have hAX' : A * X = X * B := by
    have h1 : A * X * B * B = -X * B := by rw [hAX]
    rw [Matrix.mul_assoc (A * X) B B, hB, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul] at h1
    exact neg_inj.mp h1
  obtain ⟨w, hw, hXw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hXd
  have hXu : X *ᵥ (B *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec, ← hAX', ← Matrix.mulVec_mulVec, hXw, Matrix.mulVec_zero]
  obtain ⟨u, hu⟩ : ∃ u, u = B *ᵥ w := ⟨_, rfl⟩
  rw [← hu] at hXu
  have e1 : X 0 0 * w 0 + X 0 1 * w 1 = 0 := by
    have := congr_fun hXw 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e2 : X 1 0 * w 0 + X 1 1 * w 1 = 0 := by
    have := congr_fun hXw 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e3 : X 0 0 * u 0 + X 0 1 * u 1 = 0 := by
    have := congr_fun hXu 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e4 : X 1 0 * u 0 + X 1 1 * u 1 = 0 := by
    have := congr_fun hXu 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  by_cases hδ : w 0 * u 1 - w 1 * u 0 = 0
  · obtain ⟨c, hc⟩ : ∃ c : F, u = c • w := by
      by_cases h0 : w 0 = 0
      · have h1 : w 1 ≠ 0 := by
          intro h1
          apply hw
          ext i
          fin_cases i <;> simp [h0, h1]
        refine ⟨u 1 / w 1, ?_⟩
        have hu0 : u 0 = 0 := by
          rw [h0] at hδ
          have : w 1 * u 0 = 0 := by linear_combination -hδ
          exact (mul_eq_zero.mp this).resolve_left h1
        ext i
        fin_cases i
        · simp [h0, hu0]
        · simp [h1]
      · refine ⟨u 0 / w 0, ?_⟩
        ext i
        fin_cases i
        · simp [h0]
        · simp
          field_simp
          linear_combination hδ
    have h2 : B *ᵥ u = -w := by
      rw [hu, Matrix.mulVec_mulVec, hB, Matrix.neg_mulVec, Matrix.one_mulVec]
    have h3 : B *ᵥ u = (c * c) • w := by
      rw [hc, Matrix.mulVec_smul, ← hu, hc, smul_smul]
    have h4 : (c * c + 1) • w = 0 := by
      rw [add_smul, one_smul, ← h3, h2]
      exact neg_add_cancel w
    have h5 := (smul_eq_zero.mp h4).resolve_right hw
    exact ⟨c, by linear_combination (-1 : F) * h5⟩
  · exfalso
    apply hX
    have h00 : X 0 0 = 0 := by
      have : X 0 0 * (w 0 * u 1 - w 1 * u 0) = 0 := by
        linear_combination u 1 * e1 - w 1 * e3
      exact (mul_eq_zero.mp this).resolve_right hδ
    have h01 : X 0 1 = 0 := by
      have : X 0 1 * (w 0 * u 1 - w 1 * u 0) = 0 := by
        linear_combination w 0 * e3 - u 0 * e1
      exact (mul_eq_zero.mp this).resolve_right hδ
    have h10 : X 1 0 = 0 := by
      have : X 1 0 * (w 0 * u 1 - w 1 * u 0) = 0 := by
        linear_combination u 1 * e2 - w 1 * e4
      exact (mul_eq_zero.mp this).resolve_right hδ
    have h11 : X 1 1 = 0 := by
      have : X 1 1 * (w 0 * u 1 - w 1 * u 0) = 0 := by
        linear_combination w 0 * e4 - u 0 * e2
      exact (mul_eq_zero.mp this).resolve_right hδ
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem mat_exists_isotropic_iff (h2 : (2 : F) ≠ 0) {A B : Matrix (Fin 2) (Fin 2) F}
    (hA : A * A = -1) (hAd : A.det = 1) (hB : B * B = -1) (hBd : B.det = 1) :
    (∃ X : Matrix (Fin 2) (Fin 2) F, X ≠ 0 ∧ X.det = 0 ∧ A * X * B = -X) ↔
      IsSquare (-1 : F) := by
  constructor
  · rintro ⟨X, hX, hXd, hAX⟩
    exact mat_isSquare_of_isotropic hB hX hXd hAX
  · rintro ⟨i, hi⟩
    exact mat_exists_isotropic h2 (i := i) (by linear_combination -hi) hA hAd hB hBd

end CFSG.ClassicalInvolution.RouteD.TWY
