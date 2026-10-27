module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.PSL3Four.F4 Matrix

@[expose] def tMat : Matrix (Fin 3) (Fin 3) F4 := !![1, 0, 0; 0, ω, 0; 0, 0, ω * ω]

@[expose] def tMat' : Matrix (Fin 3) (Fin 3) F4 := !![1, 0, 0; 0, ω * ω, 0; 0, 0, ω]

@[expose] def pMat : Matrix (Fin 3) (Fin 3) F4 := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem det_tMat : tMat.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

theorem det_pMat : pMat.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

@[expose] def tSL : SpecialLinearGroup (Fin 3) F4 := ⟨tMat, det_tMat⟩

@[expose] def pSL : SpecialLinearGroup (Fin 3) F4 := ⟨pMat, det_pMat⟩

theorem F4_eq_zero_of_mul (x k l : F4) (h : x * k = l * x) (hkl : k ≠ l) : x = 0 := by
  revert x k l
  decide

theorem det_eq_zero_of_tp (A : Matrix (Fin 3) (Fin 3) F4) (c d : F4) (hc : c ≠ 0)
    (h1 : A * tMat' = c • (tMat * A)) (h2 : A * pMat = d • (pMat * A)) : A.det = 0 := by
  have e1 : ∀ i j, (A * tMat') i j = (c • (tMat * A)) i j := fun i j => by rw [h1]
  have e2 : ∀ i j, (A * pMat) i j = (d • (pMat * A)) i j := fun i j => by rw [h2]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul, tMat, tMat',
    pMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.tail_cons] at e1 e2
  have z := fun i j k l (h : A i j * k = l * A i j) (hkl : k ≠ l) =>
    F4_eq_zero_of_mul (A i j) k l h hkl
  rw [Matrix.det_fin_three]
  obtain ⟨⟨c, hc4⟩⟩ := c
  interval_cases c
  · exact absurd rfl hc
  ·
    have h22 := z 2 2 ω (⟨1⟩ * (ω * ω)) (by simpa [mul_assoc] using e1 2 2) (by decide)
    have h00 : A 0 0 = 0 := by simpa [h22] using e2 0 2
    have h10 := z 1 0 1 (⟨1⟩ * ω) (by simpa [mul_assoc] using e1 1 0) (by decide)
    have h20 := z 2 0 1 (⟨1⟩ * (ω * ω)) (by simpa [mul_assoc] using e1 2 0) (by decide)
    rw [h00, h10, h20]
    ring
  ·
    have h00 := z 0 0 1 (⟨2⟩ * 1) (by simpa [mul_assoc] using e1 0 0) (by decide)
    have h11 : A 1 1 = 0 := by simpa [h00] using e2 1 0
    have h01 := z 0 1 (ω * ω) (⟨2⟩ * 1) (by simpa [mul_assoc] using e1 0 1) (by decide)
    have h21 := z 2 1 (ω * ω) (⟨2⟩ * (ω * ω)) (by simpa [mul_assoc] using e1 2 1) (by decide)
    rw [h01, h11, h21]
    ring
  ·
    have h20 := z 2 0 1 (⟨3⟩ * (ω * ω)) (by simpa [mul_assoc] using e1 2 0) (by decide)
    have h01 : A 0 1 = 0 := by simpa [h20] using e2 0 0
    have h11 := z 1 1 (ω * ω) (⟨3⟩ * ω) (by simpa [mul_assoc] using e1 1 1) (by decide)
    have h21 := z 2 1 (ω * ω) (⟨3⟩ * (ω * ω)) (by simpa [mul_assoc] using e1 2 1) (by decide)
    rw [h01, h11, h21]
    ring

theorem det_tMat' : tMat'.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

@[expose] def tSL' : SpecialLinearGroup (Fin 3) F4 := ⟨tMat', det_tMat'⟩

theorem tSL_inv : tSL⁻¹ = tSL' := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  change tMat * tMat' = 1
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem transpose_tSL' : Matrix.SpecialLinearGroup.transpose tSL' = tSL' := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose]
  change tMat'ᵀ = tMat'
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pSL_inv : pSL⁻¹ = Matrix.SpecialLinearGroup.transpose pSL := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.coe_one]
  change pMat * pMatᵀ = 1
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem transpose_transpose_pSL :
    Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transpose pSL) = pSL := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.transpose_transpose]

theorem map_frob_tSL : Matrix.SpecialLinearGroup.map frob.toRingHom tSL = tSL' := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  change frob.toRingHom.mapMatrix tMat = tMat'
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem map_frob_pSL : Matrix.SpecialLinearGroup.map frob.toRingHom pSL = pSL := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  change frob.toRingHom.mapMatrix pMat = pMat
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem exists_smul_of_proj_eq (A : GL (Fin 3) F4) (g y : SpecialLinearGroup (Fin 3) F4)
    (h : proj 3 F4 (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F4
      A g) = proj 3 F4 y) :
    ∃ c : F4, c ≠ 0 ∧ (A : Matrix (Fin 3) (Fin 3) F4) * (g : Matrix (Fin 3) (Fin 3) F4) =
      c • ((y : Matrix (Fin 3) (Fin 3) F4) * (A : Matrix (Fin 3) (Fin 3) F4)) := by
  set X := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F4 A g
    with hXdef
  obtain ⟨u, -, hu⟩ := mem_scalars.mp ((QuotientGroup.eq).1 h)
  have hX : (X : Matrix (Fin 3) (Fin 3) F4) = (A : Matrix (Fin 3) (Fin 3) F4) *
      (g : Matrix (Fin 3) (Fin 3) F4) * ((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) :=
    coe_slConjugation A g
  have hscal : ∀ M : Matrix (Fin 3) (Fin 3) F4,
      M * Matrix.scalar (Fin 3) (u : F4) = (u : F4) • M := by
    intro M
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]
  have hy : (y : Matrix (Fin 3) (Fin 3) F4) = (u : F4) • (X : Matrix (Fin 3) (Fin 3) F4) := by
    have h1 : y = X * (X⁻¹ * y) := by group
    calc (y : Matrix (Fin 3) (Fin 3) F4)
        = ((X * (X⁻¹ * y) : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) := by
          rw [← h1]
      _ = (X : Matrix (Fin 3) (Fin 3) F4) *
          ((X⁻¹ * y : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) :=
          Matrix.SpecialLinearGroup.coe_mul _ _
      _ = (u : F4) • (X : Matrix (Fin 3) (Fin 3) F4) := by rw [hu, hscal]
  have hAinv : ((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *
      (A : Matrix (Fin 3) (Fin 3) F4) = 1 := A.inv_mul
  refine ⟨(u : F4)⁻¹, inv_ne_zero u.ne_zero, ?_⟩
  rw [hy, hX, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ u.ne_zero, one_smul,
    Matrix.mul_assoc _ _ (A : Matrix (Fin 3) (Fin 3) F4), hAinv, Matrix.mul_one]

theorem det_ne_zero_GL (A : GL (Fin 3) F4) : (A : Matrix (Fin 3) (Fin 3) F4).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det A.mul_inv
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem not_fix_dual (A : GL (Fin 3) F4)
    (ht : (conjAut 3 F4 A * dualAut 3 F4) (proj 3 F4 tSL) = proj 3 F4 tSL)
    (hp : (conjAut 3 F4 A * dualAut 3 F4) (proj 3 F4 pSL) = proj 3 F4 pSL) : False := by
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj, tSL_inv, transpose_tSL'] at ht
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj, pSL_inv, transpose_transpose_pSL] at hp
  obtain ⟨c, hc, h1⟩ := exists_smul_of_proj_eq A _ _ ht
  obtain ⟨d, -, h2⟩ := exists_smul_of_proj_eq A _ _ hp
  exact det_ne_zero_GL A (det_eq_zero_of_tp _ c d hc h1 h2)

theorem not_fix_field (A : GL (Fin 3) F4)
    (ht : (conjAut 3 F4 A * fieldAut 3 F4 frob) (proj 3 F4 tSL) = proj 3 F4 tSL)
    (hp : (conjAut 3 F4 A * fieldAut 3 F4 frob) (proj 3 F4 pSL) = proj 3 F4 pSL) : False := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, map_frob_tSL] at ht
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, map_frob_pSL] at hp
  obtain ⟨c, hc, h1⟩ := exists_smul_of_proj_eq A _ _ ht
  obtain ⟨d, -, h2⟩ := exists_smul_of_proj_eq A _ _ hp
  exact det_ne_zero_GL A (det_eq_zero_of_tp _ c d hc h1 h2)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
