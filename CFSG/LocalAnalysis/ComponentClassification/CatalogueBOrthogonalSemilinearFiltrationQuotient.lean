module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearFiltrationField

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration

open CatalogueBOrthogonalSemilinear

universe u

variable {K : Type u} [Field K] {d : ℕ}

abbrev LinearIsometryQuotient (Q : QuadraticForm K (Fin d → K)) :=
  linearSimilarityPairs Q ⧸ (matrixIsometryPairs Q).subgroupOf (linearSimilarityPairs Q)

@[expose] def multiplierQuotientEquivRange (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) :
    LinearIsometryQuotient Q ≃* (multiplierHom Q hQ).range :=
  (QuotientGroup.quotientMulEquivOfEq (multiplierHom_kernel Q hQ).symm).trans
    (QuotientGroup.quotientKerEquivRange (multiplierHom Q hQ))

theorem multiplierQuotientEquivRange_mk (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) (g : linearSimilarityPairs Q) :
    (multiplierQuotientEquivRange Q hQ
      ((QuotientGroup.mk' ((matrixIsometryPairs Q).subgroupOf (linearSimilarityPairs Q)))
        g)).val = multiplier Q g.val := rfl

theorem linearIsometryQuotient_commutative (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) : IsMulCommutative (LinearIsometryQuotient Q) := by
  constructor
  constructor
  intro a b
  apply (multiplierQuotientEquivRange Q hQ).injective
  rw [map_mul, map_mul]
  exact mul_comm _ _

theorem linear_commutator_le_isometry (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) :
    ⁅linearSimilarityPairs Q, linearSimilarityPairs Q⁆ ≤ matrixIsometryPairs Q := by
  have h : commutator (linearSimilarityPairs Q) ≤
      (matrixIsometryPairs Q).subgroupOf (linearSimilarityPairs Q) := by
    rw [← multiplierHom_kernel Q hQ]
    exact Abelianization.commutator_subset_ker (multiplierHom Q hQ)
  have hm := Subgroup.map_mono (f := (linearSimilarityPairs Q).subtype) h
  simpa only [commutator, Subgroup.map_commutator, Subgroup.map_top,
    Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le (matrixIsometryPairs_le_linearPairs Q)] using hm

theorem similarity_commutator_le_linear [Finite K] (Q : QuadraticForm K (Fin d → K)) :
    commutator (similarityPairs Q) ≤ linearSimilarityPairs Q := by
  let : IsCyclic (fieldProjection Q).range := fieldProjection_range_cyclic Q
  have h := Abelianization.commutator_subset_ker (fieldProjection Q).rangeRestrict
  rwa [MonoidHom.ker_rangeRestrict] at h

abbrev SimilarityIsometryQuotient (Q : QuadraticForm K (Fin d → K)) :=
  similarityPairs Q ⧸ matrixIsometryPairs Q

theorem similarity_secondDerived_le_isometry [Finite K]
    (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0) :
    derivedSeries (similarityPairs Q) 2 ≤ matrixIsometryPairs Q := by
  change ⁅commutator (similarityPairs Q), commutator (similarityPairs Q)⁆ ≤ _
  exact (Subgroup.commutator_mono (similarity_commutator_le_linear Q)
    (similarity_commutator_le_linear Q)).trans (linear_commutator_le_isometry Q hQ)

theorem similarityIsometryQuotient_secondDerived [Finite K]
    (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0) :
    derivedSeries (SimilarityIsometryQuotient Q) 2 = ⊥ := by
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (matrixIsometryPairs Q))]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
  exact similarity_secondDerived_le_isometry Q hQ

theorem quadratic_semilinear_multiplier_filtration [Finite K]
    (hd : 1 ≤ d) (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0) :
    (matrixIsometryPairs Q).Normal ∧
    ((matrixIsometryPairs Q).subgroupOf (linearSimilarityPairs Q)).Normal ∧
    (linearSimilarityPairs Q).Normal ∧
    (fieldProjection Q).ker = linearSimilarityPairs Q ∧
    (multiplierHom Q (exists_nonzero_value Q hQ)).ker =
      (matrixIsometryPairs Q).subgroupOf (linearSimilarityPairs Q) ∧
    IsCyclic (fieldProjection Q).range ∧
    IsCyclic (similarityPairs Q ⧸ linearSimilarityPairs Q) ∧
    IsMulCommutative (LinearIsometryQuotient Q) ∧
    derivedSeries (SimilarityIsometryQuotient Q) 2 = ⊥ := by
  have _hd := hd
  exact ⟨inferInstance, inferInstance, inferInstance, rfl,
    multiplierHom_kernel Q (exists_nonzero_value Q hQ), fieldProjection_range_cyclic Q,
    fieldQuotient_cyclic Q, linearIsometryQuotient_commutative Q (exists_nonzero_value Q hQ),
    similarityIsometryQuotient_secondDerived Q (exists_nonzero_value Q hQ)⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
