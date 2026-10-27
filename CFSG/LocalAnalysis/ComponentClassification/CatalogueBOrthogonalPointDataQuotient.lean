module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataEmbedding

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open Matrix CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointAction

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem scalarMatrixLinearEquiv (c : Kˣ) (v : Fin d → K) :
    matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) c) v = (c : K) • v := by
  rw [matrixLinearEquiv_apply, GeneralLinearGroup.coe_scalar]
  funext i
  exact Matrix.mulVec_diagonal (fun _ => (c : K)) v i

@[expose] def derivedPointAction (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q →* Equiv.Perm (Points Q) :=
  (similarityPointAction Q).comp (matrixDerivedInclusion Q)

theorem derivedPointAction_submodule (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) (L : Points Q) :
    (derivedPointAction Q A L).val = L.val.map (matrixLinearEquiv A.val).toLinearMap := rfl

theorem derivedScalars_fix_point (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) (hA : A ∈ matrixDerivedScalars Q) (L : Points Q) :
    derivedPointAction Q A L = L := by
  obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q A).mp hA
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  change similarityPointMap Q (matrixDerivedInclusion Q A) (pointMk x hx hQx) = _
  rw [similarityPointMap_pointMk]
  apply (pointMk_eq_iff _ hx _ hQx).mpr
  refine ⟨(c : K), ?_⟩
  rw [matrixDerivedInclusion_val, coordinateSemilinearMap_inl, ← hc,
    scalarMatrixLinearEquiv]

theorem derivedScalars_le_pointKernel (Q : QuadraticForm K (Fin d → K)) :
    matrixDerivedScalars Q ≤ (derivedPointAction Q).ker := by
  intro A hA
  apply Equiv.ext
  exact derivedScalars_fix_point Q A hA

@[expose] def projectivePointAction (Q : QuadraticForm K (Fin d → K)) :
    matrixProjectiveDerived Q →* Equiv.Perm (Points Q) :=
  QuotientGroup.lift (matrixDerivedScalars Q) (derivedPointAction Q)
    (derivedScalars_le_pointKernel Q)

theorem projectivePointAction_mk (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) :
    projectivePointAction Q (matrixProjectiveProjection Q A) = derivedPointAction Q A :=
  QuotientGroup.lift_mk' _ _ A

theorem projectivePointAction_mk_submodule (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) (L : Points Q) :
    (projectivePointAction Q (matrixProjectiveProjection Q A) L).val =
      L.val.map (matrixLinearEquiv A.val).toLinearMap := by
  rw [projectivePointAction_mk, derivedPointAction_submodule]

theorem projectivePointAction_range_le_similarity (Q : QuadraticForm K (Fin d → K)) :
    (projectivePointAction Q).range ≤ (similarityPointAction Q).range := by
  rintro phi ⟨g, rfl⟩
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q g
  exact ⟨matrixDerivedInclusion Q A, (projectivePointAction_mk Q A).symm⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
