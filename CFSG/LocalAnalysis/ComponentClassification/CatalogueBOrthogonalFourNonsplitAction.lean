module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitHermitian
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

open Matrix

universe u

variable {K : Type u} [Field K] (delta : K)

@[expose] def normDeterminant : GL (Fin 2) (extension delta) →* Kˣ :=
  (Units.map (QuadraticAlgebra.norm : extension delta →* K)).comp GeneralLinearGroup.det

@[expose] def normDeterminantOne : Subgroup (GL (Fin 2) (extension delta)) :=
  (normDeterminant delta).ker

theorem mem_normDeterminantOne (A : GL (Fin 2) (extension delta)) :
    A ∈ normDeterminantOne delta ↔ QuadraticAlgebra.norm A.val.det = 1 := by
  change normDeterminant delta A = 1 ↔ _
  exact Units.ext_iff

theorem congruence_isHermitian (A : GL (Fin 2) (extension delta))
    (X : hermitianSubmodule delta) :
    (A.val * X.val * A.val.conjTranspose).IsHermitian := by
  change (A.val * X.val * A.val.conjTranspose).conjTranspose = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, X.property, Matrix.mul_assoc]

@[expose] def hermitianCongruence (A : GL (Fin 2) (extension delta)) :
    hermitianSubmodule delta ≃ₗ[K] hermitianSubmodule delta where
  toFun X := ⟨A.val * X.val * A.val.conjTranspose, congruence_isHermitian delta A X⟩
  invFun X := ⟨A⁻¹.val * X.val * A⁻¹.val.conjTranspose,
    congruence_isHermitian delta A⁻¹ X⟩
  left_inv X := by
    apply Subtype.ext
    change A⁻¹.val * (A.val * X.val * A.val.conjTranspose) *
      A⁻¹.val.conjTranspose = X.val
    calc
      _ = (A⁻¹.val * A.val) * X.val *
        (A.val.conjTranspose * A⁻¹.val.conjTranspose) := by
          simp only [Matrix.mul_assoc]
      _ = X.val := by
        rw [A.inv_mul, Matrix.one_mul, ← Matrix.conjTranspose_mul,
          A.inv_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  right_inv X := by
    apply Subtype.ext
    change A.val * (A⁻¹.val * X.val * A⁻¹.val.conjTranspose) *
      A.val.conjTranspose = X.val
    calc
      _ = (A.val * A⁻¹.val) * X.val *
        (A⁻¹.val.conjTranspose * A.val.conjTranspose) := by
          simp only [Matrix.mul_assoc]
      _ = X.val := by
        rw [A.mul_inv, Matrix.one_mul, ← Matrix.conjTranspose_mul,
          A.mul_inv, Matrix.conjTranspose_one, Matrix.mul_one]
  map_add' X Y := by
    apply Subtype.ext
    change A.val * (X.val + Y.val) * A.val.conjTranspose = _
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' a X := by
    apply Subtype.ext
    change A.val * (a • X.val) * A.val.conjTranspose = _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl

theorem hermitianCongruence_val (A : GL (Fin 2) (extension delta))
    (X : hermitianSubmodule delta) :
    (hermitianCongruence delta A X).val = A.val * X.val * A.val.conjTranspose := rfl

theorem hermitianCongruence_one : hermitianCongruence delta 1 = 1 := by
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  simp [hermitianCongruence_val]

theorem hermitianCongruence_mul (A B : GL (Fin 2) (extension delta)) :
    hermitianCongruence delta (A * B) =
      hermitianCongruence delta A * hermitianCongruence delta B := by
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  simp only [LinearEquiv.mul_apply, hermitianCongruence_val, Units.val_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem hermitianCongruence_form (h2 : (2 : K) ≠ 0)
    (A : GL (Fin 2) (extension delta)) (X : hermitianSubmodule delta) :
    hermitianForm delta (hermitianCongruence delta A X) =
      QuadraticAlgebra.norm A.val.det * hermitianForm delta X := by
  apply QuadraticAlgebra.algebraMap_injective (a := delta) (b := 0)
  rw [hermitianForm_det delta h2, map_mul, hermitianForm_det delta h2,
    hermitianCongruence_val, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  ring

abbrev HermitianIsometries := TauCeti.QuadraticMap.orthogonalGroup (hermitianForm delta)

@[expose] def rho (h2 : (2 : K) ≠ 0) :
    normDeterminantOne delta →* HermitianIsometries delta where
  toFun A := ⟨hermitianCongruence delta A.val,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (fun X => by
      rw [hermitianCongruence_form delta h2,
        (mem_normDeterminantOne delta A.val).mp A.property, one_mul])⟩
  map_one' := Subtype.ext (hermitianCongruence_one delta)
  map_mul' A B := Subtype.ext (hermitianCongruence_mul delta _ _)

theorem rho_val (h2 : (2 : K) ≠ 0) (A : normDeterminantOne delta)
    (X : hermitianSubmodule delta) :
    ((rho delta h2 A).val X).val = A.val.val * X.val * A.val.val.conjTranspose := rfl

@[expose] def hermitianGammaLinear : hermitianSubmodule delta ≃ₗ[K]
    hermitianSubmodule delta where
  toFun X := ⟨X.val.transpose, by
    apply Matrix.IsHermitian.ext
    intro i j
    exact X.property.apply j i⟩
  invFun X := ⟨X.val.transpose, by
    apply Matrix.IsHermitian.ext
    intro i j
    exact X.property.apply j i⟩
  left_inv X := Subtype.ext (Matrix.transpose_transpose X.val)
  right_inv X := Subtype.ext (Matrix.transpose_transpose X.val)
  map_add' X Y := Subtype.ext (Matrix.transpose_add X.val Y.val)
  map_smul' a X := Subtype.ext (Matrix.transpose_smul a X.val)

@[expose] def gamma (h2 : (2 : K) ≠ 0) : HermitianIsometries delta :=
  ⟨hermitianGammaLinear delta,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (fun X => by
      apply QuadraticAlgebra.algebraMap_injective (a := delta) (b := 0)
      rw [hermitianForm_det delta h2, hermitianForm_det delta h2]
      exact Matrix.det_transpose X.val)⟩

theorem gamma_val (h2 : (2 : K) ≠ 0) (X : hermitianSubmodule delta) :
    ((gamma delta h2).val X).val = X.val.map (conjugation delta) := by
  apply Matrix.ext
  intro i j
  exact (X.property.apply j i).symm

theorem gamma_mul_gamma (h2 : (2 : K) ≠ 0) : gamma delta h2 * gamma delta h2 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  exact Subtype.ext (Matrix.transpose_transpose X.val)

@[expose] def specialMatrices : Matrix.SpecialLinearGroup (Fin 2) (extension delta) →*
    normDeterminantOne delta where
  toFun A := ⟨Matrix.SpecialLinearGroup.toGL A, by
    rw [mem_normDeterminantOne]
    change QuadraticAlgebra.norm A.val.det = 1
    rw [A.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' A B := Subtype.ext (map_mul _ _ _)

@[expose] def specialRho (h2 : (2 : K) ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) (extension delta) →* HermitianIsometries delta :=
  (rho delta h2).comp (specialMatrices delta)

@[expose] def specialImage (h2 : (2 : K) ≠ 0) : Subgroup (HermitianIsometries delta) :=
  (specialRho delta h2).range

@[expose] def congruenceImage (h2 : (2 : K) ≠ 0) : Subgroup (HermitianIsometries delta) :=
  (rho delta h2).range

end CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
