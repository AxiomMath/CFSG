module

public import CFSG.GH74.Generic.Front.DataAbs
public import CFSG.GH74.Generic.Front.DataLA
public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis

public section

namespace CFSG.GH74.Generic

open Matrix CFSG.GH74.L5U5 CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Steinberg

variable {F : Type} [Field F] {σ : F ≃+* F}

abbrev yMat (F : Type*) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F)

theorem yMat_mul_self : yMat F * yMat F = 1 := by
  rw [yMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

theorem conjTr_diagonal_eq {n : ℕ} (v : Fin n → F) :
    conjTr σ (Matrix.diagonal v) = Matrix.diagonal fun i => σ (v i) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [conjTr]
  · simp [conjTr, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem conjTr_yMat : conjTr σ (yMat F) = yMat F := by
  rw [yMat, conjTr_diagonal_eq]
  congr 1
  ext i
  fin_cases i <;> simp

theorem conjTr_diag1 (d : F) : conjTr σ (diag1 d) = diag1 (σ d) := by
  rw [diag1, conjTr_diagonal_eq, diag1]
  congr 1
  ext i
  fin_cases i <;> simp

theorem conjTr_conjTr_of_invol (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    conjTr σ (conjTr σ M) = M := by
  ext i j
  simp [conjTr, hσ]

theorem det_conjTr_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    (conjTr σ M).det = σ M.det := by
  rw [conjTr, Matrix.det_transpose]
  have := RingHom.map_det (σ : F →+* F) M
  simpa [RingHom.mapMatrix_apply] using this.symm

theorem yMat_mul_blk4 (R S : Matrix (Fin 2) (Fin 2) F) :
    yMat F * blk4 R S = blk4 R S * yMat F := by
  rw [yMat, ← blk4_negOne_one_eq, blk4_mul, blk4_mul]
  simp

theorem exists_unitary_conj_yMat (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) ≠ 0)
    (T : Matrix (Fin 4) (Fin 4) F) (hT : T * T = 1) (hU : conjTr σ T * T = 1)
    (hdet : T.det = 1) (h1 : T ≠ 1) (hm1 : T ≠ -1) :
    ∃ P : Matrix (Fin 4) (Fin 4) F, P.det = 1 ∧ conjTr σ P * P = 1 ∧ T * P = P * yMat F := by
  obtain ⟨Q, hQ, hTQ⟩ :=
    exists_conj_diag4 h2 T hT (involution_dim_two h2 (Fintype.card_fin 4) T hT hdet h1 hm1)
  have hdQ : Q.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Q).1 hQ).ne_zero
  have hGD : conjTr σ Q * Q = yMat F * (conjTr σ Q * Q) * yMat F := by
    have e1 : conjTr σ (T * Q) * (T * Q) = conjTr σ Q * Q := by
      rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ T), hU, Matrix.one_mul]
    have e2 : conjTr σ (Q * yMat F) * (Q * yMat F) = yMat F * (conjTr σ Q * Q) * yMat F := by
      rw [conjTr_mul, conjTr_yMat]
      simp only [Matrix.mul_assoc]
    calc conjTr σ Q * Q = conjTr σ (T * Q) * (T * Q) := e1.symm
      _ = conjTr σ (Q * yMat F) * (Q * yMat F) := by rw [hTQ]
      _ = yMat F * (conjTr σ Q * Q) * yMat F := e2
  have hcomm : (conjTr σ Q * Q) * yMat F = yMat F * (conjTr σ Q * Q) := by
    calc conjTr σ Q * Q * yMat F = (yMat F * (conjTr σ Q * Q) * yMat F) * yMat F := by
          rw [← hGD]
      _ = yMat F * (conjTr σ Q * Q) * (yMat F * yMat F) := Matrix.mul_assoc _ _ _
      _ = yMat F * (conjTr σ Q * Q) := by rw [yMat_mul_self, Matrix.mul_one]
  obtain ⟨A, B, hAB⟩ := exists_blk4_of_comm h2 (g := conjTr σ Q * Q)
    (by rw [blk4_negOne_one_eq]; exact hcomm)
  have hherm : conjTr σ (conjTr σ Q * Q) = conjTr σ Q * Q := by
    rw [conjTr_mul, conjTr_conjTr_of_invol hσ.invol]
  have hdetG : (conjTr σ Q * Q).det ≠ 0 := by
    rw [Matrix.det_mul, det_conjTr_eq]
    exact mul_ne_zero ((map_ne_zero σ).2 hdQ) hdQ
  rw [hAB] at hherm hdetG
  rw [conjTr_blk4] at hherm
  obtain ⟨hA, hB⟩ := blk4_inj hherm
  rw [det_blk4] at hdetG
  obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin 2) (Fin 2) F, conjTr σ R * A * R = 1 := by
    obtain ⟨R, hR⟩ := exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution hσ hA
      (left_ne_zero_of_mul hdetG)
    exact ⟨R, hR⟩
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 2) (Fin 2) F, conjTr σ S * B * S = 1 := by
    obtain ⟨S, hS⟩ := exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution hσ hB
      (right_ne_zero_of_mul hdetG)
    exact ⟨S, hS⟩
  have hP₀U : conjTr σ (Q * blk4 R S) * (Q * blk4 R S) = 1 := by
    calc conjTr σ (Q * blk4 R S) * (Q * blk4 R S)
        = conjTr σ (blk4 R S) * (conjTr σ Q * Q) * blk4 R S := by
          rw [conjTr_mul]
          simp only [Matrix.mul_assoc]
      _ = blk4 (conjTr σ R) (conjTr σ S) * blk4 A B * blk4 R S := by
          rw [hAB, conjTr_blk4]
      _ = blk4 (conjTr σ R * A * R) (conjTr σ S * B * S) := by
          rw [blk4_mul, blk4_mul]
      _ = 1 := by rw [hR, hS, blk4_one]
  have hP₀T : T * (Q * blk4 R S) = (Q * blk4 R S) * yMat F := by
    calc T * (Q * blk4 R S)
        = (T * Q) * blk4 R S := by rw [← Matrix.mul_assoc]
      _ = Q * yMat F * blk4 R S := by rw [hTQ]
      _ = Q * (yMat F * blk4 R S) := Matrix.mul_assoc _ _ _
      _ = Q * (blk4 R S * yMat F) := by rw [yMat_mul_blk4]
      _ = Q * blk4 R S * yMat F := (Matrix.mul_assoc _ _ _).symm
  generalize Q * blk4 R S = P₀ at hP₀U hP₀T
  have hdP₀ : σ P₀.det * P₀.det = 1 := by
    have := congrArg Matrix.det hP₀U
    rwa [Matrix.det_mul, det_conjTr_eq, Matrix.det_one] at this
  have hd0 : P₀.det ≠ 0 := fun h => by
    rw [h, mul_zero] at hdP₀
    exact zero_ne_one hdP₀
  refine ⟨P₀ * diag1 P₀.det⁻¹, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, det_diag1, mul_inv_cancel₀ hd0]
  · calc conjTr σ (P₀ * diag1 P₀.det⁻¹) * (P₀ * diag1 P₀.det⁻¹)
        = conjTr σ (diag1 P₀.det⁻¹) * (conjTr σ P₀ * P₀) * diag1 P₀.det⁻¹ := by
          rw [conjTr_mul]
          simp only [Matrix.mul_assoc]
      _ = conjTr σ (diag1 P₀.det⁻¹) * diag1 P₀.det⁻¹ := by rw [hP₀U, Matrix.mul_one]
      _ = diag1 (σ P₀.det⁻¹ * P₀.det⁻¹) := by rw [conjTr_diag1, diag1_mul]
      _ = 1 := by rw [map_inv₀, ← mul_inv, hdP₀, inv_one, diag1_one]
  · rw [← Matrix.mul_assoc, hP₀T, Matrix.mul_assoc, Matrix.mul_assoc, yMat]
    rw [diag1_mul_diagonal_comm]

end CFSG.GH74.Generic
