module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointReindexCovarianceBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionStated
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance

open Matrix CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointAction

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

theorem statedDerivedPointAction_reindex (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (A : StatedOmega Q0) (L : Points Q) :
    reindexPointEquiv eI Q (statedDerivedPointAction hQ A L) =
      CatalogueBOrthogonalPointData.derivedPointAction
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)
        (statedDerivedReindexEquiv eI Q hQ A) (reindexPointEquiv eI Q L) := by
  apply Subtype.ext
  rw [reindexPointEquiv_submodule]
  change (orthogonalPointAction Q (statedOrthogonalHom hQ A) L).val.map _ = _
  rw [orthogonalPointAction_submodule,
    CatalogueBOrthogonalPointData.derivedPointAction_submodule,
    reindexPointEquiv_submodule]
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨CatalogueBOrthogonalPointData.reindexVectorEquiv eI x, ⟨x, hx, rfl⟩, ?_⟩
    exact statedDerivedReindexEquiv_vector eI Q hQ A x
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨toLinEquiv ι K A.val x, ⟨x, hx, rfl⟩, ?_⟩
    exact (statedDerivedReindexEquiv_vector eI Q hQ A x).symm

theorem statedDerivedPointAction_reindex_symm (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (A : matrixDerived (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q))
    (L : Points (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) :
    (reindexPointEquiv eI Q).symm
        (CatalogueBOrthogonalPointData.derivedPointAction
          (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) A L) =
      statedDerivedPointAction hQ ((statedDerivedReindexEquiv eI Q hQ).symm A)
        ((reindexPointEquiv eI Q).symm L) := by
  apply (reindexPointEquiv eI Q).injective
  rw [Equiv.apply_symm_apply, statedDerivedPointAction_reindex,
    MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem statedDerivedPointAction_reindex_conjugation (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (A : StatedOmega Q0) :
    (reindexPointEquiv eI Q).permCongrHom (statedDerivedPointAction hQ A) =
      CatalogueBOrthogonalPointData.derivedPointAction
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)
        (statedDerivedReindexEquiv eI Q hQ A) := by
  apply Equiv.ext
  intro L
  change (reindexPointEquiv eI Q).permCongr (statedDerivedPointAction hQ A) L = _
  rw [Equiv.permCongr_apply, statedDerivedPointAction_reindex, Equiv.apply_symm_apply]

theorem statedPointAction_reindex (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (g : StatedProj (StatedOmega Q0)) (L : Points Q) :
    reindexPointEquiv eI Q (statedPointAction hQ g L) =
      CatalogueBOrthogonalPointData.projectivePointAction
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)
        (statedProjectiveReindexEquiv eI Q hQ g) (reindexPointEquiv eI Q L) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  rw [statedProjectiveReindexEquiv_mk, CatalogueBOrthogonalPointData.projectivePointAction_mk]
  change reindexPointEquiv eI Q (statedDerivedPointAction hQ A L) = _
  exact statedDerivedPointAction_reindex eI Q hQ A L

theorem statedPointAction_reindex_symm (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (g : matrixProjectiveDerived (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q))
    (L : Points (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) :
    (reindexPointEquiv eI Q).symm
        (CatalogueBOrthogonalPointData.projectivePointAction
          (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) g L) =
      statedPointAction hQ ((statedProjectiveReindexEquiv eI Q hQ).symm g)
        ((reindexPointEquiv eI Q).symm L) := by
  apply (reindexPointEquiv eI Q).injective
  rw [Equiv.apply_symm_apply, statedPointAction_reindex,
    MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem statedPointAction_reindex_conjugation (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (g : StatedProj (StatedOmega Q0)) :
    (reindexPointEquiv eI Q).permCongrHom (statedPointAction hQ g) =
      CatalogueBOrthogonalPointData.projectivePointAction
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)
        (statedProjectiveReindexEquiv eI Q hQ g) := by
  apply Equiv.ext
  intro L
  change (reindexPointEquiv eI Q).permCongr (statedPointAction hQ g) L = _
  rw [Equiv.permCongr_apply, statedPointAction_reindex, Equiv.apply_symm_apply]

theorem statedPointAction_reindex_conjugation_symm (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (g : matrixProjectiveDerived (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) :
    (reindexPointEquiv eI Q).permCongrHom.symm
        (CatalogueBOrthogonalPointData.projectivePointAction
          (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) g) =
      statedPointAction hQ ((statedProjectiveReindexEquiv eI Q hQ).symm g) := by
  apply (reindexPointEquiv eI Q).permCongrHom.injective
  rw [MulEquiv.apply_symm_apply, statedPointAction_reindex_conjugation,
    MulEquiv.apply_symm_apply]

theorem statedPointAction_reindex_submodule (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (g : StatedProj (StatedOmega Q0)) (L : Points Q) :
    (CatalogueBOrthogonalPointData.projectivePointAction
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)
        (statedProjectiveReindexEquiv eI Q hQ g) (reindexPointEquiv eI Q L)).val =
      (statedPointAction hQ g L).val.map
        (CatalogueBOrthogonalPointData.reindexVectorEquiv eI).toLinearMap := by
  rw [← statedPointAction_reindex, reindexPointEquiv_submodule]

theorem statedPointAction_reindex_symm_submodule (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (g : matrixProjectiveDerived (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q))
    (L : Points (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) :
    (statedPointAction hQ ((statedProjectiveReindexEquiv eI Q hQ).symm g)
        ((reindexPointEquiv eI Q).symm L)).val =
      (CatalogueBOrthogonalPointData.projectivePointAction
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) g L).val.map
        (CatalogueBOrthogonalPointData.reindexVectorEquiv eI).symm.toLinearMap := by
  rw [← statedPointAction_reindex_symm, reindexPointEquiv_symm_submodule]

end CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
