module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open Matrix CatalogueBHigherLinearField

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def IsCrossSimilarity (Q Q' : QuadraticForm K (Fin d → K))
    (m : coordinateSemilinearGroup d K) : Prop :=
  ∃ μ : Kˣ, ∀ v, Q' (coordinateSemilinearMap m v) = (μ : K) * m.right (Q v)

variable {Q Q' : QuadraticForm K (Fin d → K)} {m : coordinateSemilinearGroup d K}

theorem IsCrossSimilarity.inv (h : IsCrossSimilarity Q Q' m) : IsCrossSimilarity Q' Q m⁻¹ := by
  obtain ⟨μ, hμ⟩ := h
  refine ⟨Units.map m.right.symm.toMonoidHom μ⁻¹, fun v => ?_⟩
  have h1 := hμ (coordinateSemilinearMap m⁻¹ v)
  rw [coordinateSemilinearMap_inv, AddEquiv.apply_symm_apply] at h1
  rw [coordinateSemilinearMap_inv, SemidirectProduct.inv_right]
  apply m.right.injective
  rw [map_mul, h1]
  change _ = m.right (m.right.symm ((μ⁻¹ : Kˣ) : K)) * m.right (m.right.symm _)
  rw [m.right.apply_symm_apply, m.right.apply_symm_apply, ← mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mul]

theorem matrixConjugation_mem_matrixIsometries_of_cross (h : IsCrossSimilarity Q Q' m)
    {A : GL (Fin d) K} (hA : A ∈ matrixIsometries Q) :
    matrixConjugation m A ∈ matrixIsometries Q' := by
  obtain ⟨μ, hμ⟩ := h
  rw [mem_matrixIsometries_iff] at hA ⊢
  intro v
  rw [matrixConjugation_vector, hμ, hA, ← hμ, AddEquiv.apply_symm_apply]

theorem matrixIsometries_map_of_isCrossSimilarity (h : IsCrossSimilarity Q Q' m) :
    (matrixIsometries Q).map (matrixConjugation m).toMonoidHom = matrixIsometries Q' := by
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact matrixConjugation_mem_matrixIsometries_of_cross h hA
  · intro hB
    refine ⟨matrixConjugation m⁻¹ B, matrixConjugation_mem_matrixIsometries_of_cross h.inv hB, ?_⟩
    change matrixConjugationHom m (matrixConjugationHom m⁻¹ B) = B
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem matrixDerived_map_of_isCrossSimilarity (h : IsCrossSimilarity Q Q' m) :
    (matrixDerived Q).map (matrixConjugation m).toMonoidHom = matrixDerived Q' := by
  rw [matrixDerived, Subgroup.map_commutator, matrixIsometries_map_of_isCrossSimilarity h]
  rfl

@[expose] noncomputable def matrixDerivedCrossEquiv (h : IsCrossSimilarity Q Q' m) :
    matrixDerived Q ≃* matrixDerived Q' :=
  ((matrixConjugation m).subgroupMap (matrixDerived Q)).trans
    (MulEquiv.subgroupCongr (matrixDerived_map_of_isCrossSimilarity h))

theorem matrixDerivedScalars_map_cross (h : IsCrossSimilarity Q Q' m) :
    (matrixDerivedScalars Q).map (matrixDerivedCrossEquiv h).toMonoidHom =
      matrixDerivedScalars Q' := by
  have hS := matrixScalars_invariant m
  have hSinv : (matrixScalars d K).map (matrixConjugation m).symm.toMonoidHom =
      matrixScalars d K :=
    (Subgroup.map_symm_eq_iff_map_eq (matrixScalars d K)
      (H := matrixScalars d K) (e := matrixConjugation m)).mpr hS
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    change matrixConjugation m B.val ∈ matrixScalars d K
    rw [← hS]
    exact Subgroup.mem_map_of_mem (matrixConjugation m).toMonoidHom hB
  · intro hA
    refine ⟨(matrixDerivedCrossEquiv h).symm A, ?_, by simp⟩
    have hval : ((matrixDerivedCrossEquiv h).symm A).val = (matrixConjugation m).symm A.val := by
      apply (matrixConjugation m).injective
      rw [MulEquiv.apply_symm_apply]
      exact congrArg Subtype.val ((matrixDerivedCrossEquiv h).apply_symm_apply A)
    change ((matrixDerivedCrossEquiv h).symm A).val ∈ matrixScalars d K
    rw [hval, ← hSinv]
    exact Subgroup.mem_map_of_mem (matrixConjugation m).symm.toMonoidHom hA

@[expose] noncomputable def matrixProjectiveCrossEquiv (h : IsCrossSimilarity Q Q' m) :
    matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q' :=
  QuotientGroup.congr (matrixDerivedScalars Q) (matrixDerivedScalars Q')
    (matrixDerivedCrossEquiv h) (matrixDerivedScalars_map_cross h)

theorem matrixProjectiveCrossEquiv_mk (h : IsCrossSimilarity Q Q' m) (A : matrixDerived Q) :
    matrixProjectiveCrossEquiv h (matrixProjectiveProjection Q A) =
      matrixProjectiveProjection Q' (matrixDerivedCrossEquiv h A) :=
  QuotientGroup.congr_mk' _ _ _ _ A

theorem IsCrossSimilarity.conj_mem_similarityPairs (h : IsCrossSimilarity Q Q' m)
    (g : similarityPairs Q) : m * g.val * m⁻¹ ∈ similarityPairs Q' := by
  obtain ⟨μ', hμ'⟩ := h.inv
  obtain ⟨μ, hμ⟩ := h
  set ν := multiplier Q g with hν
  refine ⟨μ * Units.map m.right.toMonoidHom (ν * Units.map g.val.right.toMonoidHom μ'),
    fun v => ?_⟩
  rw [coordinateSemilinearMap_mul, coordinateSemilinearMap_mul, hμ, multiplier_spec, hμ']
  simp only [Units.coe_map, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mul,
    map_mul, SemidirectProduct.mul_right, SemidirectProduct.inv_right, ← hν]
  have e1 : ∀ x : K, m.right.toMonoidHom x = m.right x := fun _ => rfl
  have e2 : ∀ x : K, g.val.right.toMonoidHom x = g.val.right x := fun _ => rfl
  have e3 : (m.right * g.val.right * m.right⁻¹) (Q' v) =
      m.right (g.val.right (m.right⁻¹ (Q' v))) := rfl
  rw [e1, e1, e2, e3]
  ring

theorem congr_matrixProjectiveConjugation_cross (h : IsCrossSimilarity Q Q' m)
    (g : similarityPairs Q) :
    MulAut.congr (matrixProjectiveCrossEquiv h) (matrixProjectiveConjugation Q g) =
      matrixProjectiveConjugation Q' ⟨_, h.conj_mem_similarityPairs g⟩ := by
  apply MulEquiv.ext
  intro x
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q' x
  obtain ⟨B, hB⟩ := matrixProjectiveProjection_surjective Q
    ((matrixProjectiveCrossEquiv h).symm (matrixProjectiveProjection Q' A))
  have hA : matrixProjectiveProjection Q' A =
      matrixProjectiveCrossEquiv h (matrixProjectiveProjection Q B) := by
    rw [hB, MulEquiv.apply_symm_apply]
  simp only [MulAut.congr_apply, MulEquiv.trans_apply]
  rw [hA, MulEquiv.symm_apply_apply, matrixProjectiveConjugation_mk,
    matrixProjectiveCrossEquiv_mk, matrixProjectiveCrossEquiv_mk, matrixProjectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  change matrixConjugationHom m (matrixConjugationHom g.val B.val) =
    matrixConjugationHom (m * g.val * m⁻¹) (matrixConjugationHom m B.val)
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]

theorem congr_mem_matrixProjectiveImage_cross_iff (h : IsCrossSimilarity Q Q' m)
    (y : MulAut (matrixProjectiveDerived Q)) :
    MulAut.congr (matrixProjectiveCrossEquiv h) y ∈ matrixProjectiveImage Q' ↔
      y ∈ matrixProjectiveImage Q := by
  constructor
  · rintro ⟨g', hg'⟩
    have hg : m⁻¹ * g'.val * m⁻¹⁻¹ ∈ similarityPairs Q := h.inv.conj_mem_similarityPairs g'
    rw [inv_inv] at hg
    refine ⟨⟨_, hg⟩, (MulAut.congr (matrixProjectiveCrossEquiv h)).injective ?_⟩
    change MulAut.congr (matrixProjectiveCrossEquiv h) (matrixProjectiveConjugation Q ⟨_, hg⟩) =
      MulAut.congr (matrixProjectiveCrossEquiv h) y
    rw [congr_matrixProjectiveConjugation_cross]
    rw [← hg']
    change matrixProjectiveConjugationHom Q' _ = matrixProjectiveConjugationHom Q' g'
    congr 1
    apply Subtype.ext
    change m * (m⁻¹ * g'.val * m) * m⁻¹ = g'.val
    group
  · rintro ⟨g, rfl⟩
    exact ⟨⟨_, h.conj_mem_similarityPairs g⟩, (congr_matrixProjectiveConjugation_cross h g).symm⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
