module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointReindexCovarianceAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataNormalizer

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance

open CFSG.Assembly.LowTwoRank
open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointAction CatalogueBStabilizerFamily

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

theorem statedDerivedPointAction_range_reindex (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) :
    (statedDerivedPointAction hQ).range.map (reindexPointEquiv eI Q).permCongrHom.toMonoidHom =
      (CatalogueBOrthogonalPointData.derivedPointAction
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)).range := by
  ext phi
  constructor
  · rintro ⟨psi, ⟨A, rfl⟩, rfl⟩
    exact ⟨statedDerivedReindexEquiv eI Q hQ A,
      (statedDerivedPointAction_reindex_conjugation eI Q hQ A).symm⟩
  · rintro ⟨A, rfl⟩
    refine ⟨statedDerivedPointAction hQ ((statedDerivedReindexEquiv eI Q hQ).symm A),
      ⟨(statedDerivedReindexEquiv eI Q hQ).symm A, rfl⟩, ?_⟩
    change (reindexPointEquiv eI Q).permCongrHom
      (statedDerivedPointAction hQ ((statedDerivedReindexEquiv eI Q hQ).symm A)) = _
    rw [statedDerivedPointAction_reindex_conjugation eI Q hQ, MulEquiv.apply_symm_apply]

theorem statedPointAction_range_reindex (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) :
    (statedPointAction hQ).range.map (reindexPointEquiv eI Q).permCongrHom.toMonoidHom =
      (CatalogueBOrthogonalPointData.projectivePointAction
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)).range := by
  ext phi
  constructor
  · rintro ⟨psi, ⟨g, rfl⟩, rfl⟩
    exact ⟨statedProjectiveReindexEquiv eI Q hQ g,
      (statedPointAction_reindex_conjugation eI Q hQ g).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨statedPointAction hQ ((statedProjectiveReindexEquiv eI Q hQ).symm g),
      ⟨(statedProjectiveReindexEquiv eI Q hQ).symm g, rfl⟩, ?_⟩
    change (reindexPointEquiv eI Q).permCongrHom
      (statedPointAction hQ ((statedProjectiveReindexEquiv eI Q hQ).symm g)) = _
    rw [statedPointAction_reindex_conjugation eI Q hQ, MulEquiv.apply_symm_apply]

theorem statedPointAction_range_reindex_symm (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) :
    (CatalogueBOrthogonalPointData.projectivePointAction
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)).range.map
        (reindexPointEquiv eI Q).permCongrHom.symm.toMonoidHom =
      (statedPointAction hQ).range :=
  (Subgroup.map_symm_eq_iff_map_eq (statedPointAction hQ).range
    (e := (reindexPointEquiv eI Q).permCongrHom)).mpr
      (statedPointAction_range_reindex eI Q hQ)

@[expose] def statedPointStabilizer {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K}
    (hQ : ⇑Q = Q0) (L : Points Q) : Subgroup (StatedProj (StatedOmega Q0)) :=
  pointStabilizer (statedPointAction hQ) L

theorem mem_statedPointStabilizer_iff {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K}
    (hQ : ⇑Q = Q0) (L : Points Q) (g : StatedProj (StatedOmega Q0)) :
    g ∈ statedPointStabilizer hQ L ↔ statedPointAction hQ g L = L := Iff.rfl

theorem statedPointStabilizer_reindex_comap (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) (L : Points Q) :
    (CatalogueBOrthogonalPointData.projectivePointStabilizer
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) (reindexPointEquiv eI Q L)).comap
        (statedProjectiveReindexEquiv eI Q hQ).toMonoidHom = statedPointStabilizer hQ L := by
  ext g
  change CatalogueBOrthogonalPointData.projectivePointAction _
    (statedProjectiveReindexEquiv eI Q hQ g) (reindexPointEquiv eI Q L) =
    reindexPointEquiv eI Q L ↔ statedPointAction hQ g L = L
  rw [← statedPointAction_reindex eI Q hQ g L]
  exact (reindexPointEquiv eI Q).injective.eq_iff

theorem statedPointStabilizer_reindex_map (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) (L : Points Q) :
    (statedPointStabilizer hQ L).map (statedProjectiveReindexEquiv eI Q hQ).toMonoidHom =
      CatalogueBOrthogonalPointData.projectivePointStabilizer
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) (reindexPointEquiv eI Q L) := by
  rw [← statedPointStabilizer_reindex_comap eI Q hQ L]
  exact Subgroup.map_comap_eq_self_of_surjective (statedProjectiveReindexEquiv eI Q hQ).surjective _

theorem statedPointStabilizer_reindex_symm_map (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (L : Points (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) :
    (CatalogueBOrthogonalPointData.projectivePointStabilizer
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) L).map
        (statedProjectiveReindexEquiv eI Q hQ).symm.toMonoidHom =
      statedPointStabilizer hQ ((reindexPointEquiv eI Q).symm L) := by
  apply (Subgroup.map_symm_eq_iff_map_eq
    (statedPointStabilizer hQ ((reindexPointEquiv eI Q).symm L))
    (e := statedProjectiveReindexEquiv eI Q hQ)).mpr
  change (statedPointStabilizer hQ ((reindexPointEquiv eI Q).symm L)).map
    (statedProjectiveReindexEquiv eI Q hQ).toMonoidHom = _
  rw [statedPointStabilizer_reindex_map eI Q hQ, Equiv.apply_symm_apply]

@[expose] def statedPointFamily {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K}
    (hQ : ⇑Q = Q0) : Set (Subgroup (StatedProj (StatedOmega Q0))) :=
  family (statedPointAction hQ)

theorem statedPointFamily_reindex (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) :
    (fun U => U.map (statedProjectiveReindexEquiv eI Q hQ).toMonoidHom) '' statedPointFamily hQ =
      CatalogueBOrthogonalPointData.projectivePointFamily
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) := by
  ext U
  constructor
  · rintro ⟨T, ⟨L, rfl⟩, rfl⟩
    exact ⟨reindexPointEquiv eI Q L, (statedPointStabilizer_reindex_map eI Q hQ L).symm⟩
  · rintro ⟨L, rfl⟩
    refine ⟨statedPointStabilizer hQ ((reindexPointEquiv eI Q).symm L),
      ⟨(reindexPointEquiv eI Q).symm L, rfl⟩, ?_⟩
    change (statedPointStabilizer hQ ((reindexPointEquiv eI Q).symm L)).map
      (statedProjectiveReindexEquiv eI Q hQ).toMonoidHom =
      CatalogueBOrthogonalPointData.projectivePointStabilizer
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) L
    rw [statedPointStabilizer_reindex_map eI Q hQ, Equiv.apply_symm_apply]

theorem statedPointFamily_reindex_symm (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) :
    (fun U => U.map (statedProjectiveReindexEquiv eI Q hQ).symm.toMonoidHom) ''
        CatalogueBOrthogonalPointData.projectivePointFamily
          (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) = statedPointFamily hQ := by
  ext U
  constructor
  · rintro ⟨T, ⟨L, rfl⟩, rfl⟩
    exact ⟨(reindexPointEquiv eI Q).symm L,
      (statedPointStabilizer_reindex_symm_map eI Q hQ L).symm⟩
  · rintro ⟨L, rfl⟩
    refine ⟨CatalogueBOrthogonalPointData.projectivePointStabilizer
      (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) (reindexPointEquiv eI Q L),
      ⟨reindexPointEquiv eI Q L, rfl⟩, ?_⟩
    change (CatalogueBOrthogonalPointData.projectivePointStabilizer
      (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) (reindexPointEquiv eI Q L)).map
      (statedProjectiveReindexEquiv eI Q hQ).symm.toMonoidHom = statedPointStabilizer hQ L
    rw [statedPointStabilizer_reindex_symm_map eI Q hQ, Equiv.symm_apply_apply]

@[expose] def statedPointNormalizer {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K}
    (hQ : ⇑Q = Q0) : Subgroup (Equiv.Perm (Points Q)) := imageNormalizer (statedPointAction hQ)

theorem statedPointNormalizer_reindex_map (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) :
    (statedPointNormalizer hQ).map (reindexPointEquiv eI Q).permCongrHom.toMonoidHom =
      CatalogueBOrthogonalPointData.projectivePointNormalizer
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) := by
  have h := Subgroup.map_equiv_normalizer_eq (statedPointAction hQ).range
    (reindexPointEquiv eI Q).permCongrHom
  rw [statedPointAction_range_reindex eI Q hQ] at h
  exact h

@[expose] def statedPointNormalizerReindexEquiv (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0) :
    statedPointNormalizer hQ ≃*
      CatalogueBOrthogonalPointData.projectivePointNormalizer
        (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q) :=
  ((reindexPointEquiv eI Q).permCongrHom.subgroupMap (statedPointNormalizer hQ)).trans
    (MulEquiv.subgroupCongr (statedPointNormalizer_reindex_map eI Q hQ))

theorem statedPointNormalizerReindexEquiv_apply (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (phi : statedPointNormalizer hQ)
    (L : Points (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) :
    (statedPointNormalizerReindexEquiv eI Q hQ phi).val L =
      reindexPointEquiv eI Q (phi.val ((reindexPointEquiv eI Q).symm L)) := rfl

theorem statedPointNormalizerReindexEquiv_symm_apply (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (phi : CatalogueBOrthogonalPointData.projectivePointNormalizer
      (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) (L : Points Q) :
    ((statedPointNormalizerReindexEquiv eI Q hQ).symm phi).val L =
      (reindexPointEquiv eI Q).symm (phi.val (reindexPointEquiv eI Q L)) := rfl

theorem statedPointNormalizerReindexEquiv_submodule (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (phi : statedPointNormalizer hQ)
    (L : Points (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) :
    ((statedPointNormalizerReindexEquiv eI Q hQ phi).val L).val =
      (phi.val ((reindexPointEquiv eI Q).symm L)).val.map
        (CatalogueBOrthogonalPointData.reindexVectorEquiv eI).toLinearMap := by
  rw [statedPointNormalizerReindexEquiv_apply, reindexPointEquiv_submodule]

theorem statedPointNormalizerReindexEquiv_symm_submodule (eI : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) {Q0 : (ι → K) → K} (hQ : ⇑Q = Q0)
    (phi : CatalogueBOrthogonalPointData.projectivePointNormalizer
      (CatalogueBOrthogonalPointData.reindexQuadraticForm eI Q)) (L : Points Q) :
    (((statedPointNormalizerReindexEquiv eI Q hQ).symm phi).val L).val =
      (phi.val (reindexPointEquiv eI Q L)).val.map
        (CatalogueBOrthogonalPointData.reindexVectorEquiv eI).symm.toLinearMap := by
  rw [statedPointNormalizerReindexEquiv_symm_apply, reindexPointEquiv_symm_submodule]

end CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
