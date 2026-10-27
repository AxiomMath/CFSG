module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroBasic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonal

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K]

theorem traceZero_conjugate_trace (A : GL (Fin 2) K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    (A.val * X * A⁻¹.val).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, A.inv_mul, Matrix.one_mul]

@[expose] def traceZeroConjugation (A : GL (Fin 2) K) :
    traceZeroSubmodule K ≃ₗ[K] traceZeroSubmodule K where
  toFun X := ⟨A.val * X.val * A⁻¹.val, by
    change (A.val * X.val * A⁻¹.val).trace = 0
    rw [traceZero_conjugate_trace]
    exact X.property⟩
  invFun X := ⟨A⁻¹.val * X.val * A.val, by
    change (A⁻¹.val * X.val * A.val).trace = 0
    have h := traceZero_conjugate_trace A⁻¹ X.val
    rw [inv_inv] at h
    rw [h]
    exact X.property⟩
  left_inv X := by
    apply Subtype.ext
    change A⁻¹.val * (A.val * X.val * A⁻¹.val) * A.val = X.val
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹.val A.val,
      A.inv_mul, Matrix.one_mul, Matrix.mul_one]
  right_inv X := by
    apply Subtype.ext
    change A.val * (A⁻¹.val * X.val * A.val) * A⁻¹.val = X.val
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc A.val A⁻¹.val,
      A.mul_inv, Matrix.one_mul, Matrix.mul_one]
  map_add' X Y := by
    apply Subtype.ext
    change A.val * (X.val + Y.val) * A⁻¹.val = _
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' a X := by
    apply Subtype.ext
    change A.val * (a • X.val) * A⁻¹.val = _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl

theorem traceZeroConjugation_val (A : GL (Fin 2) K) (X : traceZeroSubmodule K) :
    (traceZeroConjugation A X).val = A.val * X.val * A⁻¹.val := rfl

theorem traceZeroConjugation_form (A : GL (Fin 2) K) (X : traceZeroSubmodule K) :
    traceZeroForm K (traceZeroConjugation A X) = traceZeroForm K X := by
  rw [traceZeroForm_eq_neg_det, traceZeroForm_eq_neg_det, traceZeroConjugation_val,
    Matrix.det_mul, Matrix.det_mul]
  have hdet : A.val.det * A⁻¹.val.det = 1 := by
    rw [← Matrix.det_mul, A.mul_inv, Matrix.det_one]
  congr 1
  calc
    A.val.det * X.val.det * A⁻¹.val.det =
        (A.val.det * A⁻¹.val.det) * X.val.det := by ring
    _ = X.val.det := by rw [hdet, one_mul]

@[expose] def traceZeroOrthogonalAction :
    GL (Fin 2) K →* TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K) where
  toFun A := ⟨traceZeroConjugation A,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (traceZeroConjugation_form A)⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    simp [traceZeroConjugation_val]
  map_mul' A B := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    change (A * B).val * X.val * (A * B)⁻¹.val =
      A.val * (B.val * X.val * B⁻¹.val) * A⁻¹.val
    simp only [Units.val_mul, _root_.mul_inv_rev, Matrix.mul_assoc]

theorem traceZeroOrthogonalAction_val (A : GL (Fin 2) K) (X : traceZeroSubmodule K) :
    ((traceZeroOrthogonalAction A).val X).val = A.val * X.val * A⁻¹.val := rfl

end CFSG.ComponentClassification.CatalogueBOrthogonal
