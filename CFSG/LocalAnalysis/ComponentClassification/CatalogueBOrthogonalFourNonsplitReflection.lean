module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K] (delta : K)

@[expose] def alternatingTwo : GL (Fin 2) (extension delta) :=
  { val := !![0, 1; -1, 0]
    inv := !![0, -1; 1, 0]
    val_inv := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    inv_val := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] }

theorem alternatingTwo_val : (alternatingTwo delta).val = !![0, 1; -1, 0] := rfl

theorem alternatingTwo_det : (alternatingTwo delta).val.det = 1 := by
  simp [alternatingTwo_val, Matrix.det_fin_two]

theorem alternating_conjugate_eq_adjugate (X : hermitianSubmodule delta) :
    (alternatingTwo delta).val * X.val.transpose *
      (alternatingTwo delta).val.conjTranspose = X.val.adjugate := by
  rw [alternatingTwo_val, Matrix.adjugate_fin_two]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem hermitian_adjugate_polar (h2 : (2 : K) ≠ 0)
    (X Y : hermitianSubmodule delta) :
    X.val * Y.val.adjugate + Y.val * X.val.adjugate =
      (hermitianForm delta).polarBilin X Y • (1 : Matrix (Fin 2) (Fin 2) (extension delta)) := by
  have h : (X.val + Y.val) * (X.val + Y.val).adjugate =
      (X.val + Y.val).det • (1 : Matrix (Fin 2) (Fin 2) (extension delta)) :=
    Matrix.mul_adjugate _
  have hadj : (X.val + Y.val).adjugate = X.val.adjugate + Y.val.adjugate := by
    rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
    all_goals abel
  rw [hadj, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_adjugate,
    Matrix.mul_adjugate] at h
  have hp : (X.val + Y.val).det = X.val.det + Y.val.det +
      algebraMap K (extension delta) ((hermitianForm delta).polarBilin X Y) := by
    change (X + Y).val.det = X.val.det + Y.val.det + _
    rw [← hermitianForm_det delta h2 X, ← hermitianForm_det delta h2 Y,
      ← hermitianForm_det delta h2 (X + Y), polarBilin_apply_apply, polar]
    simp only [map_sub]
    ring
  rw [hp, add_smul, add_smul] at h
  have hs : algebraMap K (extension delta) ((hermitianForm delta).polarBilin X Y) •
      (1 : Matrix (Fin 2) (Fin 2) (extension delta)) =
      (hermitianForm delta).polarBilin X Y •
        (1 : Matrix (Fin 2) (Fin 2) (extension delta)) := by
    apply Matrix.ext
    intro i j
    simp [Algebra.smul_def]
  rw [hs] at h
  linear_combination (norm := abel) h

theorem hermitian_adjugate_triple (h2 : (2 : K) ≠ 0)
    (X Y : hermitianSubmodule delta) :
    X.val * Y.val.adjugate * X.val =
      (hermitianForm delta).polarBilin X Y • X.val - hermitianForm delta X • Y.val := by
  have h := congrArg (fun Z : Matrix (Fin 2) (Fin 2) (extension delta) => Z * X.val)
    (hermitian_adjugate_polar delta h2 X Y)
  rw [Matrix.add_mul, Matrix.mul_assoc Y.val, Matrix.adjugate_mul,
    ← hermitianForm_det delta h2 X] at h
  have hs : algebraMap K (extension delta) (hermitianForm delta X) •
      (1 : Matrix (Fin 2) (Fin 2) (extension delta)) =
      hermitianForm delta X • (1 : Matrix (Fin 2) (Fin 2) (extension delta)) := by
    apply Matrix.ext
    intro i j
    simp [Algebra.smul_def]
  rw [hs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at h
  exact eq_sub_of_add_eq h

theorem hermitianCongruence_scalar (c : (extension delta)ˣ)
    (X : hermitianSubmodule delta) :
    (hermitianCongruence delta (GeneralLinearGroup.scalar (Fin 2) c) X).val =
      QuadraticAlgebra.norm (c : extension delta) • X.val := by
  rw [hermitianCongruence_val, GeneralLinearGroup.coe_scalar]
  have hs : (Matrix.scalar (Fin 2) (c : extension delta)) =
      (c : extension delta) • (1 : Matrix (Fin 2) (Fin 2) (extension delta)) := by
    change Matrix.diagonal (fun _ : Fin 2 => (c : extension delta)) = _
    apply Matrix.ext
    intro i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [hs, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  rw [mul_comm (star (c : extension delta)) (c : extension delta)]
  rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  apply Matrix.ext
  intro i j
  simp [Algebra.smul_def]

variable [Fact (¬ IsSquare delta)]

@[expose] def hermitianAnisotropicGL (h2 : (2 : K) ≠ 0)
    (X : hermitianSubmodule delta) (hX : hermitianForm delta X ≠ 0) :
    GL (Fin 2) (extension delta) :=
  GeneralLinearGroup.mkOfDetNeZero X.val (by
    rw [← hermitianForm_det delta h2]
    exact (map_ne_zero (algebraMap K (extension delta))).mpr hX)

theorem hermitianAnisotropicGL_val (h2 : (2 : K) ≠ 0)
    (X : hermitianSubmodule delta) (hX : hermitianForm delta X ≠ 0) :
    (hermitianAnisotropicGL delta h2 X hX).val = X.val := rfl

theorem exists_reflection_coefficient [Finite K]
    (h2 : (2 : K) ≠ 0) (X : hermitianSubmodule delta)
    (hX : hermitianForm delta X ≠ 0) :
    ∃ c : (extension delta)ˣ,
      QuadraticAlgebra.norm (c : extension delta) = -(hermitianForm delta X)⁻¹ := by
  obtain ⟨c, hc⟩ := extension_norm_surjective delta h2 (-(Units.mk0 _ hX)⁻¹)
  exact ⟨c, hc⟩

@[expose] def hermitianReflectionGL (h2 : (2 : K) ≠ 0)
    (X : hermitianSubmodule delta) (hX : hermitianForm delta X ≠ 0)
    (c : (extension delta)ˣ) : GL (Fin 2) (extension delta) :=
  GeneralLinearGroup.scalar (Fin 2) c * hermitianAnisotropicGL delta h2 X hX *
    alternatingTwo delta

theorem hermitianReflectionGL_mem (h2 : (2 : K) ≠ 0)
    (X : hermitianSubmodule delta) (hX : hermitianForm delta X ≠ 0)
    (c : (extension delta)ˣ)
    (hc : QuadraticAlgebra.norm (c : extension delta) = -(hermitianForm delta X)⁻¹) :
    hermitianReflectionGL delta h2 X hX c ∈ normDeterminantOne delta := by
  rw [mem_normDeterminantOne]
  change QuadraticAlgebra.norm
    ((GeneralLinearGroup.scalar (Fin 2) c).val *
      (hermitianAnisotropicGL delta h2 X hX).val * (alternatingTwo delta).val).det = 1
  rw [Matrix.det_mul, Matrix.det_mul, alternatingTwo_det,
    hermitianAnisotropicGL_val, ← hermitianForm_det delta h2]
  have hscalar : (GeneralLinearGroup.scalar (Fin 2) c).val.det = (c : extension delta) ^ 2 := by
    rw [GeneralLinearGroup.coe_scalar]
    simp [Matrix.scalar, pow_two]
  rw [hscalar, mul_one, map_mul, map_pow, hc, QuadraticAlgebra.norm_algebraMap]
  field_simp

theorem hermitianReflectionGL_formula (h2 : (2 : K) ≠ 0)
    (X : hermitianSubmodule delta) (hX : hermitianForm delta X ≠ 0)
    (c : (extension delta)ˣ)
    (hc : QuadraticAlgebra.norm (c : extension delta) = -(hermitianForm delta X)⁻¹)
    (Y : hermitianSubmodule delta) :
    (hermitianCongruence delta (hermitianReflectionGL delta h2 X hX c)
      ((gamma delta h2).val Y)).val =
        Y.val - ((hermitianForm delta).polarBilin X Y / hermitianForm delta X) • X.val := by
  rw [hermitianReflectionGL, hermitianCongruence_mul, hermitianCongruence_mul]
  change (hermitianCongruence delta (GeneralLinearGroup.scalar (Fin 2) c)
    (hermitianCongruence delta (hermitianAnisotropicGL delta h2 X hX)
      (hermitianCongruence delta (alternatingTwo delta) ((gamma delta h2).val Y)))).val = _
  rw [hermitianCongruence_scalar, hc, hermitianCongruence_val,
    hermitianAnisotropicGL_val, X.property]
  change -(hermitianForm delta X)⁻¹ •
    (X.val * ((alternatingTwo delta).val * Y.val.transpose *
      (alternatingTwo delta).val.conjTranspose) * X.val) = _
  rw [alternating_conjugate_eq_adjugate, hermitian_adjugate_triple delta h2,
    smul_sub, smul_smul, smul_smul]
  simp only [neg_mul, inv_mul_cancel₀ hX, neg_smul, one_smul,
    div_eq_mul_inv]
  rw [mul_comm]
  abel

theorem hermitian_reflection_eq_rho_gamma [Finite K]
    (h2 : (2 : K) ≠ 0) (X : hermitianSubmodule delta)
    [Invertible (hermitianForm delta X)] :
    ∃ A : normDeterminantOne delta,
      TauCeti.QuadraticMap.reflectionOrthogonal (hermitianForm delta) X =
        rho delta h2 A * gamma delta h2 := by
  have hX := (isUnit_of_invertible (hermitianForm delta X)).ne_zero
  obtain ⟨c, hc⟩ := exists_reflection_coefficient delta h2 X hX
  refine ⟨⟨hermitianReflectionGL delta h2 X hX c,
    hermitianReflectionGL_mem delta h2 X hX c hc⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro Y
  apply Subtype.ext
  rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal,
    TauCeti.QuadraticMap.reflection_apply_eq_sub_div]
  exact (hermitianReflectionGL_formula delta h2 X hX c hc Y).symm

end CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
