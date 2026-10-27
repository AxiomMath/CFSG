module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataScalarPairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open CatalogueBDerivedNormalSection

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem matrixDerivedPairs_eq_sectionDerived (Q : QuadraticForm K (Fin d → K)) :
    matrixDerivedPairs Q = derivedNormalSubgroup (matrixIsometryPairs Q) := by
  rw [matrixDerivedPairs_eq_commutator, derivedNormalSubgroup_eq]

@[expose] def matrixSectionDerivedEquiv (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q ≃* derivedNormalSubgroup (matrixIsometryPairs Q) :=
  (matrixDerivedPairEquiv Q).trans
    (MulEquiv.subgroupCongr (matrixDerivedPairs_eq_sectionDerived Q))

theorem matrixSectionDerivedEquiv_val (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) :
    (matrixSectionDerivedEquiv Q A : similarityPairs Q) = matrixDerivedInclusion Q A := rfl

theorem matrixScalarPairs_le_sectionDerived (Q : QuadraticForm K (Fin d → K)) :
    matrixScalarPairs Q ≤ derivedNormalSubgroup (matrixIsometryPairs Q) := by
  rw [← matrixDerivedPairs_eq_sectionDerived]
  exact matrixScalarPairs_le_derivedPairs Q

theorem matrixDerivedScalars_map_sectionEquiv (Q : QuadraticForm K (Fin d → K)) :
    (matrixDerivedScalars Q).map (matrixSectionDerivedEquiv Q).toMonoidHom =
      sectionDenominator (matrixIsometryPairs Q) (matrixScalarPairs Q) := by
  ext g
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, rfl⟩
  · rintro ⟨A, hA, hAg⟩
    exact ⟨A, hA, Subtype.ext hAg⟩

theorem matrixSectionDerivedEquiv_conjugation (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (A : matrixDerived Q) :
    matrixSectionDerivedEquiv Q (matrixDerivedConjugation Q g A) =
      sectionConjugation (matrixIsometryPairs Q) g (matrixSectionDerivedEquiv Q A) := by
  apply Subtype.ext
  rw [sectionConjugation_apply, matrixSectionDerivedEquiv_val,
    matrixSectionDerivedEquiv_val]
  exact matrixDerivedInclusion_conjugation Q g A

@[expose] def matrixSectionEquiv (Q : QuadraticForm K (Fin d → K)) :
    matrixProjectiveDerived Q ≃*
      Section (matrixIsometryPairs Q) (matrixScalarPairs Q) :=
  QuotientGroup.congr (matrixDerivedScalars Q)
    (sectionDenominator (matrixIsometryPairs Q) (matrixScalarPairs Q))
    (matrixSectionDerivedEquiv Q) (matrixDerivedScalars_map_sectionEquiv Q)

theorem matrixSectionEquiv_mk (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) :
    matrixSectionEquiv Q (matrixProjectiveProjection Q A) =
      sectionProjection (matrixIsometryPairs Q) (matrixScalarPairs Q)
        (matrixSectionDerivedEquiv Q A) :=
  QuotientGroup.congr_mk' _ _ _ _ A

theorem matrixSectionEquiv_action (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (x : matrixProjectiveDerived Q) :
    matrixSectionEquiv Q (matrixProjectiveConjugationHom Q g x) =
      quotientConjugationHom (matrixIsometryPairs Q) (matrixScalarPairs Q) g
        (matrixSectionEquiv Q x) := by
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change matrixSectionEquiv Q
    (matrixProjectiveConjugation Q g (matrixProjectiveProjection Q A)) = _
  rw [matrixProjectiveConjugation_mk, matrixSectionEquiv_mk, matrixSectionEquiv_mk]
  change _ = sectionAutomorphism (matrixIsometryPairs Q) (matrixScalarPairs Q) g _
  rw [sectionAutomorphism_mk, matrixSectionDerivedEquiv_conjugation]

theorem matrixSectionEquiv_congr (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) :
    MulAut.congr (matrixSectionEquiv Q) (matrixProjectiveConjugationHom Q g) =
      quotientConjugationHom (matrixIsometryPairs Q) (matrixScalarPairs Q) g := by
  apply MulEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (matrixSectionEquiv Q).surjective y
  change matrixSectionEquiv Q
    (matrixProjectiveConjugationHom Q g
      ((matrixSectionEquiv Q).symm (matrixSectionEquiv Q x))) = _
  rw [MulEquiv.symm_apply_apply]
  exact matrixSectionEquiv_action Q g x

theorem matrixProjectiveConjugationHom_derived (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) :
    matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q A) =
      MulAut.conj (matrixProjectiveProjection Q A) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change matrixProjectiveConjugation Q (matrixDerivedInclusion Q A)
    (matrixProjectiveProjection Q B) = _
  rw [matrixProjectiveConjugation_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem matrixProjective_inner_le_image (Q : QuadraticForm K (Fin d → K)) :
    OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ matrixProjectiveImage Q := by
  rintro alpha ⟨x, rfl⟩
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  exact ⟨matrixDerivedInclusion Q A, matrixProjectiveConjugationHom_derived Q A⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
