module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataReindexGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryPoints

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance

open Matrix CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointAction

universe u v

section Points

variable {K : Type u} [Field K] {ι : Type v} {d : ℕ}

@[expose] def reindexPointEquiv (eI : ι ≃ Fin d) (Q : QuadraticForm K (ι → K)) :
    Points Q ≃ Points (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) :=
  CatalogueBOrthogonalPointIsometry.pointIsometryEquiv
    (CatalogueBOrthogonalPointData.reindexQuadraticIsometry eI Q)

theorem reindexPointEquiv_submodule (eI : ι ≃ Fin d) (Q : QuadraticForm K (ι → K))
    (L : Points Q) :
    (reindexPointEquiv eI Q L).val =
      L.val.map (CatalogueBOrthogonalPointData.reindexVectorEquiv eI).toLinearMap := rfl

theorem reindexPointEquiv_symm_submodule (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K))
    (L : Points (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) :
    ((reindexPointEquiv eI Q).symm L).val =
      L.val.map (CatalogueBOrthogonalPointData.reindexVectorEquiv eI).symm.toLinearMap := rfl

theorem mem_reindexPointEquiv (eI : ι ≃ Fin d) (Q : QuadraticForm K (ι → K))
    (L : Points Q) (x : Fin d → K) :
    x ∈ (reindexPointEquiv eI Q L).val ↔ (fun i => x (eI i)) ∈ L.val :=
  CatalogueBOrthogonalPointIsometry.mem_pointIsometryEquiv
    (CatalogueBOrthogonalPointData.reindexQuadraticIsometry eI Q) L x

theorem mem_reindexPointEquiv_symm (eI : ι ≃ Fin d) (Q : QuadraticForm K (ι → K))
    (L : Points (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) (x : ι → K) :
    x ∈ ((reindexPointEquiv eI Q).symm L).val ↔ (fun i => x (eI.symm i)) ∈ L.val :=
  CatalogueBOrthogonalPointIsometry.mem_pointIsometryEquiv_symm
    (CatalogueBOrthogonalPointData.reindexQuadraticIsometry eI Q) L x

end Points

section Matrices

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

@[expose] def statedDerivedReindexEquiv (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) :
    StatedOmega Q0 ≃*
      matrixDerived (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) := by
  subst Q0
  exact CatalogueBOrthogonalPointData.statedMatrixDerivedEquiv eI Q

theorem statedDerivedReindexEquiv_val (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (A : StatedOmega Q0) :
    (statedDerivedReindexEquiv eI Q hQ A).val =
      CatalogueBOrthogonalPointData.reindexMatrixEquiv eI A.val := by
  subst Q0
  exact CatalogueBOrthogonalPointData.statedMatrixDerivedEquiv_val eI Q A

theorem statedDerivedReindexEquiv_symm_val (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (A : matrixDerived (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) :
    ((statedDerivedReindexEquiv eI Q hQ).symm A).val =
      (CatalogueBOrthogonalPointData.reindexMatrixEquiv eI).symm A.val := by
  apply (CatalogueBOrthogonalPointData.reindexMatrixEquiv eI).injective
  rw [← statedDerivedReindexEquiv_val eI Q hQ, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]

theorem statedDerivedReindexEquiv_entry (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (A : StatedOmega Q0) (i j : Fin d) :
    (statedDerivedReindexEquiv eI Q hQ A).val.val i j =
      A.val.val (eI.symm i) (eI.symm j) := by
  rw [statedDerivedReindexEquiv_val]
  rfl

theorem statedDerivedReindexEquiv_symm_entry (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (A : matrixDerived (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) (i j : ι) :
    ((statedDerivedReindexEquiv eI Q hQ).symm A).val.val i j = A.val.val (eI i) (eI j) := by
  rw [statedDerivedReindexEquiv_symm_val]
  rfl

theorem statedDerivedReindexEquiv_vector (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (A : StatedOmega Q0) (x : ι → K) :
    matrixLinearEquiv (statedDerivedReindexEquiv eI Q hQ A).val
        (CatalogueBOrthogonalPointData.reindexVectorEquiv eI x) =
      CatalogueBOrthogonalPointData.reindexVectorEquiv eI (toLinEquiv ι K A.val x) := by
  rw [statedDerivedReindexEquiv_val]
  exact CatalogueBOrthogonalPointData.reindexMatrixEquiv_mulVec eI A.val x

theorem statedDerivedReindexEquiv_symm_vector (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (A : matrixDerived (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q))
    (x : Fin d → K) :
    toLinEquiv ι K ((statedDerivedReindexEquiv eI Q hQ).symm A).val
        ((CatalogueBOrthogonalPointData.reindexVectorEquiv eI).symm x) =
      (CatalogueBOrthogonalPointData.reindexVectorEquiv eI).symm
        (matrixLinearEquiv A.val x) := by
  apply (CatalogueBOrthogonalPointData.reindexVectorEquiv eI).injective
  rw [← statedDerivedReindexEquiv_vector eI Q hQ, MulEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem statedDerivedReindexEquiv_scalars (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) :
    ((StatedScalars ι K).subgroupOf (StatedOmega Q0)).map
        (statedDerivedReindexEquiv eI Q hQ).toMonoidHom =
      matrixDerivedScalars (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) := by
  subst Q0
  exact CatalogueBOrthogonalPointData.statedMatrixDerivedEquiv_scalars eI Q

@[expose] def statedProjectiveReindexEquiv (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) :
    StatedProj (StatedOmega Q0) ≃*
      matrixProjectiveDerived (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) := by
  subst Q0
  exact CatalogueBOrthogonalPointData.statedMatrixProjectiveEquiv eI Q

theorem statedProjectiveReindexEquiv_mk (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (A : StatedOmega Q0) :
    statedProjectiveReindexEquiv eI Q hQ (QuotientGroup.mk' _ A) =
      matrixProjectiveProjection (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)
        (statedDerivedReindexEquiv eI Q hQ A) := by
  subst Q0
  exact CatalogueBOrthogonalPointData.statedMatrixProjectiveEquiv_mk eI Q A

theorem statedProjectiveReindexEquiv_symm_mk (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (A : matrixDerived (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) :
    (statedProjectiveReindexEquiv eI Q hQ).symm
        (matrixProjectiveProjection (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) A) =
      QuotientGroup.mk' _ ((statedDerivedReindexEquiv eI Q hQ).symm A) := by
  apply (statedProjectiveReindexEquiv eI Q hQ).injective
  rw [MulEquiv.apply_symm_apply, statedProjectiveReindexEquiv_mk,
    MulEquiv.apply_symm_apply]

end Matrices

end CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
