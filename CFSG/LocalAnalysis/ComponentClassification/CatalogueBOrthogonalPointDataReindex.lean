module

public import CFSG.ClassicalGroups.Orthogonal.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open Matrix CatalogueBOrthogonalSemilinear
open CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank

universe u v

variable {K : Type u} [Field K]
variable {ι : Type v} {d : ℕ}

@[expose] def reindexVectorEquiv (e : ι ≃ Fin d) :
    (ι → K) ≃ₗ[K] (Fin d → K) :=
  (LinearEquiv.funCongrLeft K K e).symm

theorem reindexVectorEquiv_apply (e : ι ≃ Fin d) (v : ι → K) (i : Fin d) :
    reindexVectorEquiv (K := K) e v i = v (e.symm i) := rfl

theorem reindexVectorEquiv_symm_apply (e : ι ≃ Fin d) (v : Fin d → K) (i : ι) :
    (reindexVectorEquiv (K := K) e).symm v i = v (e i) := rfl

variable [Fintype ι] [DecidableEq ι]

@[expose] def reindexMatrixEquiv (e : ι ≃ Fin d) : GL ι K ≃* GL (Fin d) K :=
  Units.mapEquiv (Matrix.reindexRingEquiv K e).toMulEquiv

theorem reindexMatrixEquiv_val (e : ι ≃ Fin d) (A : GL ι K) :
    (reindexMatrixEquiv e A).val = Matrix.reindex e e A.val := rfl

theorem reindexMatrixEquiv_symm_val (e : ι ≃ Fin d) (A : GL (Fin d) K) :
    ((reindexMatrixEquiv e).symm A).val = Matrix.reindex e.symm e.symm A.val := rfl

theorem reindexMatrixEquiv_mulVec (e : ι ≃ Fin d) (A : GL ι K) (v : ι → K) :
    matrixLinearEquiv (reindexMatrixEquiv e A) (reindexVectorEquiv e v) =
      reindexVectorEquiv e (A.val *ᵥ v) := by
  rw [matrixLinearEquiv_apply, reindexMatrixEquiv_val]
  funext i
  change (A.val.submatrix e.symm e.symm *ᵥ (v ∘ e.symm)) i = (A.val *ᵥ v) (e.symm i)
  have hv : (v ∘ e.symm) ∘ e = v := by
    funext j
    exact congrArg v (e.symm_apply_apply j)
  have h := Matrix.submatrix_mulVec_equiv A.val (v ∘ e.symm) e.symm e.symm
  simpa only [Equiv.symm_symm, hv, Function.comp_apply] using congrFun h i

@[expose] def reindexQuadraticForm (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K)) :
    QuadraticForm K (Fin d → K) :=
  Q.comp (reindexVectorEquiv e).symm.toLinearMap

omit [Fintype ι] [DecidableEq ι] in
theorem reindexQuadraticForm_apply (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K))
    (v : Fin d → K) :
    reindexQuadraticForm e Q v = Q (fun i => v (e i)) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem reindexQuadraticForm_map (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K))
    (v : ι → K) : reindexQuadraticForm e Q (reindexVectorEquiv e v) = Q v := by
  change Q ((reindexVectorEquiv e).symm (reindexVectorEquiv e v)) = Q v
  rw [LinearEquiv.symm_apply_apply]

@[expose] def reindexQuadraticIsometry (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K)) :
    Q.IsometryEquiv (reindexQuadraticForm e Q) where
  toLinearEquiv := reindexVectorEquiv e
  map_app' := reindexQuadraticForm_map e Q

theorem reindexMatrixEquiv_scalar (e : ι ≃ Fin d) (a : Kˣ) :
    reindexMatrixEquiv e (GeneralLinearGroup.scalar ι a) =
      GeneralLinearGroup.scalar (Fin d) a := by
  apply Units.ext
  rw [reindexMatrixEquiv_val, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply]
  simp only [e.symm.injective.eq_iff]

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
