module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonal

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K]

@[expose] def traceZeroAnisotropicGL (X : traceZeroSubmodule K)
    (hX : traceZeroForm K X ≠ 0) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero X.val (by
    rw [← neg_ne_zero, ← traceZeroForm_eq_neg_det]
    exact hX)

theorem traceZeroAnisotropicGL_val (X : traceZeroSubmodule K)
    (hX : traceZeroForm K X ≠ 0) : (traceZeroAnisotropicGL X hX).val = X.val := rfl

theorem traceZeroAnisotropicGL_inv (X : traceZeroSubmodule K)
    (hX : traceZeroForm K X ≠ 0) :
    (traceZeroAnisotropicGL X hX)⁻¹.val = (traceZeroForm K X)⁻¹ • X.val := by
  rw [GeneralLinearGroup.coe_inv, traceZeroAnisotropicGL_val]
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, traceZero_square, smul_smul, inv_mul_cancel₀ hX, one_smul]

theorem traceZero_triple (X Y : traceZeroSubmodule K) :
    X.val * Y.val * X.val =
      (traceZeroForm K).polarBilin X Y • X.val - traceZeroForm K X • Y.val := by
  have h := congrArg (fun Z : Matrix (Fin 2) (Fin 2) K => Z * X.val)
    (traceZero_anticommutator X Y)
  rw [Matrix.add_mul, Matrix.mul_assoc Y.val, traceZero_square,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at h
  exact eq_sub_of_add_eq h

theorem traceZeroAnisotropic_conjugation_val (X : traceZeroSubmodule K)
    (hX : traceZeroForm K X ≠ 0) (Y : traceZeroSubmodule K) :
    (traceZeroConjugation (traceZeroAnisotropicGL X hX) Y).val =
      ((traceZeroForm K).polarBilin X Y / traceZeroForm K X) • X.val - Y.val := by
  rw [traceZeroConjugation_val, traceZeroAnisotropicGL_val,
    traceZeroAnisotropicGL_inv, Matrix.mul_smul, traceZero_triple,
    smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hX, one_smul]
  rw [div_eq_mul_inv, mul_comm]

theorem traceZero_reflection_eq_neg_conjugation (X : traceZeroSubmodule K)
    [Invertible (traceZeroForm K X)] :
    TauCeti.QuadraticMap.reflectionOrthogonal (traceZeroForm K) X =
      QuadraticMap.negOrthogonal (traceZeroForm K) *
        traceZeroOrthogonalAction
          (traceZeroAnisotropicGL X (isUnit_of_invertible _).ne_zero) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro Y
  apply Subtype.ext
  rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal, Subgroup.coe_mul,
    QuadraticMap.coe_negOrthogonal]
  change (TauCeti.QuadraticMap.reflection (traceZeroForm K) X Y).val =
    -(traceZeroConjugation
      (traceZeroAnisotropicGL X (isUnit_of_invertible _).ne_zero) Y).val
  rw [TauCeti.QuadraticMap.reflection_apply_eq_sub_div,
    traceZeroAnisotropic_conjugation_val]
  change Y.val - ((traceZeroForm K).polarBilin X Y / traceZeroForm K X) • X.val =
    -(((traceZeroForm K).polarBilin X Y / traceZeroForm K X) • X.val - Y.val)
  abel

end CFSG.ComponentClassification.CatalogueBOrthogonal
