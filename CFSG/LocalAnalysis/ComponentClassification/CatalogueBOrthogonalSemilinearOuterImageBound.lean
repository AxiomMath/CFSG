module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImageTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearFiltrationQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImage

open CatalogueBOrthogonalSemilinear CatalogueBDerivedNormalSection

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem matrixImageInner_map_original (Q : QuadraticForm K (Fin d → K)) :
    (matrixImageInner Q).map (matrixProjectiveImage Q).subtype =
      OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
  Subgroup.map_subgroupOf_eq_of_le (matrixProjective_inner_le_image Q)

theorem matrixDerivedPairs_le_innerQuotientKernel (Q : QuadraticForm K (Fin d → K)) :
    matrixDerivedPairs Q ≤ (matrixInnerQuotientAction Q).ker := by
  rintro g ⟨A, rfl⟩
  change matrixImageInnerProjection Q ((matrixProjectiveConjugationHom Q).rangeRestrict
    (matrixDerivedInclusion Q A)) = 1
  apply (QuotientGroup.eq_one_iff (N := matrixImageInner Q) _).mpr
  change matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q A) ∈
    OuterAutomorphisms.inner (matrixProjectiveDerived Q)
  exact ⟨matrixProjectiveProjection Q A, (matrixProjectiveConjugationHom_derived Q A).symm⟩

theorem matrixInnerQuotientAction_derivedSeries_bot_of_quotient
    (Q : QuadraticForm K (Fin d → K)) (r : ℕ)
    (hquotient : derivedSeries (similarityPairs Q ⧸ matrixIsometryPairs Q) r = ⊥) :
    derivedSeries (MatrixImageInnerQuotient Q) (r + 1) = ⊥ := by
  have hderived : derivedSeries (similarityPairs Q) (r + 1) ≤ matrixDerivedPairs Q := by
    rw [matrixDerivedPairs_eq_sectionDerived]
    exact derivedSeries_succ_le_derivedNormalSubgroup (matrixIsometryPairs Q) r hquotient
  rw [← map_derivedSeries_eq (matrixInnerQuotientAction_surjective Q)]
  exact (Subgroup.map_eq_bot_iff _).mpr
    (hderived.trans (matrixDerivedPairs_le_innerQuotientKernel Q))

theorem matrixOuterAction_range_derivedSeries_bot_of_quotient
    (Q : QuadraticForm K (Fin d → K)) (r : ℕ)
    (hquotient : derivedSeries (similarityPairs Q ⧸ matrixIsometryPairs Q) r = ⊥) :
    derivedSeries (matrixOuterAction Q).range (r + 1) = ⊥ :=
  (matrixImageInnerQuotient_derivedSeries_iff Q (r + 1)).mp
    (matrixInnerQuotientAction_derivedSeries_bot_of_quotient Q r hquotient)

theorem matrixImageInnerQuotient_thirdDerived [Finite K]
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0) :
    derivedSeries (MatrixImageInnerQuotient Q) 3 = ⊥ :=
  matrixInnerQuotientAction_derivedSeries_bot_of_quotient Q 2
    (CatalogueBOrthogonalSemilinearFiltration.similarityIsometryQuotient_secondDerived Q
      (CatalogueBOrthogonalSemilinearFiltration.exists_nonzero_value Q hQ))

theorem matrixOuterAction_range_thirdDerived [Finite K]
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0) :
    derivedSeries (matrixOuterAction Q).range 3 = ⊥ :=
  (matrixImageInnerQuotient_derivedSeries_iff Q 3).mp
    (matrixImageInnerQuotient_thirdDerived Q hQ)

theorem matrixImageInnerQuotient_solvable [Finite K]
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0) :
    Group.IsSolvable (MatrixImageInnerQuotient Q) :=
  ⟨⟨3, matrixImageInnerQuotient_thirdDerived Q hQ⟩⟩

theorem quadratic_semilinear_outer_image_solvable [Finite K]
    (hd : 1 ≤ d) (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0) :
    OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ matrixProjectiveImage Q ∧
      ((OuterAutomorphisms.inner (matrixProjectiveDerived Q)).subgroupOf
        (matrixProjectiveImage Q)).Normal ∧
      ((OuterAutomorphisms.inner (matrixProjectiveDerived Q)).subgroupOf
        (matrixProjectiveImage Q)).map (matrixProjectiveImage Q).subtype =
        OuterAutomorphisms.inner (matrixProjectiveDerived Q) ∧
      (matrixImageOuterHom Q).ker =
        (OuterAutomorphisms.inner (matrixProjectiveDerived Q)).subgroupOf
          (matrixProjectiveImage Q) ∧
      derivedSeries (matrixProjectiveImage Q ⧸
        (OuterAutomorphisms.inner (matrixProjectiveDerived Q)).subgroupOf
          (matrixProjectiveImage Q)) 3 = ⊥ ∧
      Group.IsSolvable (matrixProjectiveImage Q ⧸
        (OuterAutomorphisms.inner (matrixProjectiveDerived Q)).subgroupOf
          (matrixProjectiveImage Q)) := by
  have _hd := hd
  exact ⟨matrixProjective_inner_le_image Q, inferInstance, matrixImageInner_map_original Q,
    matrixImageOuterHom_kernel Q, matrixImageInnerQuotient_thirdDerived Q hQ,
    matrixImageInnerQuotient_solvable Q hQ⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImage
