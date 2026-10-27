module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataReindex
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open Matrix CatalogueBOrthogonalSemilinear
open CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

theorem reindexMatrixEquiv_mem_isometries (e : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) (A : GL ι K) :
    reindexMatrixEquiv e A ∈ matrixIsometries (reindexQuadraticForm e Q) ↔
      A ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).comap (toLinEquiv ι K).toMonoidHom := by
  rw [mem_matrixIsometries_iff, Subgroup.mem_comap,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · intro h v
    have hv := h (reindexVectorEquiv e v)
    rw [reindexMatrixEquiv_mulVec, reindexQuadraticForm_map, reindexQuadraticForm_map] at hv
    simpa only [MulEquiv.coe_toMonoidHom, toLinEquiv_apply] using hv
  · intro h v
    obtain ⟨w, rfl⟩ := (reindexVectorEquiv e).surjective v
    rw [reindexMatrixEquiv_mulVec, reindexQuadraticForm_map, reindexQuadraticForm_map]
    simpa only [MulEquiv.coe_toMonoidHom, toLinEquiv_apply] using h w

theorem stated_isometries_reindex (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K)) :
    (Subgroup.closure {A : GL ι K | ∀ v, Q (A.val *ᵥ v) = Q v}).map
        (reindexMatrixEquiv e).toMonoidHom = matrixIsometries (reindexQuadraticForm e Q) := by
  rw [closure_isometries_eq_comap (Q := Q) rfl]
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact (reindexMatrixEquiv_mem_isometries e Q B).mpr hB
  · intro hA
    refine ⟨(reindexMatrixEquiv e).symm A, ?_, (reindexMatrixEquiv e).apply_symm_apply A⟩
    apply (reindexMatrixEquiv_mem_isometries e Q _).mp
    simpa only [MulEquiv.apply_symm_apply] using hA

theorem stated_derived_reindex (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K)) :
    (StatedOmega (⇑Q)).map (reindexMatrixEquiv e).toMonoidHom =
      matrixDerived (reindexQuadraticForm e Q) := by
  rw [StatedOmega, Subgroup.map_commutator, stated_isometries_reindex]
  rfl

@[expose] def statedMatrixDerivedEquiv (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K)) :
    StatedOmega (⇑Q) ≃* matrixDerived (reindexQuadraticForm e Q) :=
  ((reindexMatrixEquiv e).subgroupMap (StatedOmega (⇑Q))).trans
    (MulEquiv.subgroupCongr (stated_derived_reindex e Q))

theorem statedMatrixDerivedEquiv_val (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K))
    (A : StatedOmega (⇑Q)) :
    (statedMatrixDerivedEquiv e Q A).val = reindexMatrixEquiv e A.val := rfl

theorem statedMatrixDerivedEquiv_scalars (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K)) :
    ((StatedScalars ι K).subgroupOf (StatedOmega (⇑Q))).map
        (statedMatrixDerivedEquiv e Q).toMonoidHom =
      matrixDerivedScalars (reindexQuadraticForm e Q) := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨a, ha⟩ := hB
    change GeneralLinearGroup.scalar ι a = B.val at ha
    apply (mem_matrixDerivedScalars_iff _ _).mpr
    refine ⟨a, ?_⟩
    change GeneralLinearGroup.scalar (Fin d) a = (statedMatrixDerivedEquiv e Q B).val
    rw [statedMatrixDerivedEquiv_val, ← ha, reindexMatrixEquiv_scalar]
  · intro hA
    let B := (statedMatrixDerivedEquiv e Q).symm A
    refine ⟨B, ?_, (statedMatrixDerivedEquiv e Q).apply_symm_apply A⟩
    obtain ⟨a, ha⟩ := (mem_matrixDerivedScalars_iff _ A).mp hA
    have hval : reindexMatrixEquiv e B.val = A.val := by
      have h := congrArg Subtype.val ((statedMatrixDerivedEquiv e Q).apply_symm_apply A)
      exact h
    change ∃ c : Kˣ, GeneralLinearGroup.scalar ι c = B.val
    refine ⟨a, (reindexMatrixEquiv e).injective ?_⟩
    rw [reindexMatrixEquiv_scalar, hval]
    exact ha

@[expose] def statedMatrixProjectiveEquiv (e : ι ≃ Fin d)
    (Q : QuadraticForm K (ι → K)) :
    StatedProj (StatedOmega (⇑Q)) ≃* matrixProjectiveDerived (reindexQuadraticForm e Q) :=
  QuotientGroup.congr _ _ (statedMatrixDerivedEquiv e Q) (statedMatrixDerivedEquiv_scalars e Q)

theorem statedMatrixProjectiveEquiv_mk (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K))
    (A : StatedOmega (⇑Q)) :
    statedMatrixProjectiveEquiv e Q (QuotientGroup.mk' _ A) =
      matrixProjectiveProjection (reindexQuadraticForm e Q) (statedMatrixDerivedEquiv e Q A) :=
  QuotientGroup.congr_mk' _ _ _ _ A

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
