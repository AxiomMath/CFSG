module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Sym
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Frame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.UniLow

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def Aw (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, -1]

@[expose] def Gw (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![2, -1; -1, 2]

theorem Aw_cube : Aw K ^ 3 = 1 := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Aw, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem Aw_det : (Aw K).det = 1 := by
  simp [Aw, Matrix.det_fin_two_of]

theorem Gw_det : (Gw K).det = 3 := by
  simp [Gw, Matrix.det_fin_two_of]
  ring

theorem Aw_gram : (Aw K)ᵀ * Gw K * Aw K = Gw K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Aw, Gw, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem dagI_Gw (h : UnitaryFieldData p f K) : KU7.dagI h (Gw K) = Gw K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KU7.dagI, Gw, map_ofNat]

theorem dagI_Aw (h : UnitaryFieldData p f K) : KU7.dagI h (Aw K) = (Aw K)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KU7.dagI, Aw]

theorem exists_gram_frame [Finite K] (h : UnitaryFieldData p f K) (h3 : (3 : K) ≠ 0) :
    ∃ P : GL (Fin 2) K,
      KU7.dagI h (P : Matrix (Fin 2) (Fin 2) K) * Gw K * (P : Matrix (Fin 2) (Fin 2) K) = 1 := by
  have hdet : (Gw K).det ≠ 0 := by
    rw [Gw_det]
    exact h3
  have hu : IsUnit (Gw K) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨P, hP⟩ := CFSG.ComponentClassification.CatalogueBHermitian.exists_orthonormal_matrix
    (KU7.barEq h) (KU7.barEq_sq h) (KU7.barEq_ne_one h) hu.unit
    (by rw [IsUnit.unit_spec, KU7.conjTr_barEq, dagI_Gw])
  refine ⟨P, ?_⟩
  rw [IsUnit.unit_spec, KU7.conjTr_barEq] at hP
  exact hP

theorem exists_block [Finite K] (h : UnitaryFieldData p f K) (h3 : (3 : K) ≠ 0) :
    ∃ B : Matrix (Fin 2) (Fin 2) K, KU7.dagI h B * B = 1 ∧ B.det = 1 ∧ B ^ 3 = 1 ∧
      (∀ c : K, B ≠ c • 1) ∧ (∀ c : K, B ^ 2 ≠ c • 1) := by
  obtain ⟨P, hP⟩ := exists_gram_frame h h3
  set Pm : Matrix (Fin 2) (Fin 2) K := (P : Matrix (Fin 2) (Fin 2) K) with hPm
  set Qi : Matrix (Fin 2) (Fin 2) K := ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hQi
  have hQP : Qi * Pm = 1 := by
    rw [hQi, hPm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPQ : Pm * Qi = 1 := by
    rw [hQi, hPm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdQ : KU7.dagI h Qi * Qi = Gw K := by
    have hdPQ : KU7.dagI h Qi * KU7.dagI h Pm = 1 := by
      rw [← KU7.dagI_mul, hPQ]
      unfold KU7.dagI
      simp
    calc KU7.dagI h Qi * Qi
        = KU7.dagI h Qi * (KU7.dagI h Pm * Gw K * Pm) * Qi := by rw [hP, mul_one]
      _ = (KU7.dagI h Qi * KU7.dagI h Pm) * Gw K * (Pm * Qi) := by
          simp only [mul_assoc]
      _ = Gw K := by rw [hdPQ, hPQ, one_mul, mul_one]
  set B : Matrix (Fin 2) (Fin 2) K := Qi * Aw K * Pm with hB
  have hdB : KU7.dagI h B = KU7.dagI h Pm * (Aw K)ᵀ * KU7.dagI h Qi := by
    rw [hB, KU7.dagI_mul, KU7.dagI_mul, dagI_Aw, mul_assoc]
  have hB1 : KU7.dagI h B * B = 1 := by
    rw [hdB, hB]
    calc KU7.dagI h Pm * (Aw K)ᵀ * KU7.dagI h Qi * (Qi * Aw K * Pm)
        = KU7.dagI h Pm * ((Aw K)ᵀ * (KU7.dagI h Qi * Qi) * Aw K) * Pm := by
          simp only [mul_assoc]
      _ = KU7.dagI h Pm * ((Aw K)ᵀ * Gw K * Aw K) * Pm := by rw [hdQ]
      _ = KU7.dagI h Pm * Gw K * Pm := by rw [Aw_gram]
      _ = 1 := hP
  have hB3 : B ^ 3 = 1 := by
    rw [hB, pow_three']
    calc Qi * Aw K * Pm * (Qi * Aw K * Pm) * (Qi * Aw K * Pm)
        = Qi * (Aw K * (Pm * Qi) * Aw K * (Pm * Qi) * Aw K) * Pm := by
          simp only [mul_assoc]
      _ = Qi * (Aw K * Aw K * Aw K) * Pm := by rw [hPQ]; simp only [mul_one, mul_assoc]
      _ = Qi * (Aw K ^ 3) * Pm := by rw [pow_three']
      _ = 1 := by rw [Aw_cube, mul_one, hQP]
  have hdet : B.det = 1 := by
    rw [hB, Matrix.det_mul, Matrix.det_mul]
    have hdd : Qi.det * Pm.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    calc Qi.det * (Aw K).det * Pm.det = (Qi.det * Pm.det) * (Aw K).det := by ring
      _ = 1 := by rw [hdd, Aw_det, one_mul]
  have hns1 : ∀ c : K, B ≠ c • 1 := by
    intro c hc
    have hA : Aw K = c • 1 := by
      have key : Pm * B * Qi = Aw K := by
        rw [hB]
        calc Pm * (Qi * Aw K * Pm) * Qi = (Pm * Qi) * Aw K * (Pm * Qi) := by
              simp only [mul_assoc]
          _ = Aw K := by rw [hPQ, one_mul, mul_one]
      rw [← key, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPQ]
    have h01 := congrFun (congrFun hA 0) 1
    simp [Aw] at h01
  refine ⟨B, hB1, hdet, hB3, hns1, ?_⟩
  intro c hc
  apply hns1 (c * c)
  have hB4 : B ^ 4 = B := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hB3, one_mul]
  calc B = B ^ 4 := hB4.symm
    _ = (B ^ 2) ^ 2 := by rw [← pow_mul]
    _ = (c * c) • 1 := by rw [hc, sq, Matrix.smul_mul, Matrix.one_mul, smul_smul]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.UniLow

end
