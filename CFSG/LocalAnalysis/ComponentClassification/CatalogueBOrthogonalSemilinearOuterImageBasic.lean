module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImage

open CatalogueBOrthogonalSemilinear

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def matrixOuterAction (Q : QuadraticForm K (Fin d → K)) :
    similarityPairs Q →* OuterAutomorphisms.Outer (matrixProjectiveDerived Q) :=
  (QuotientGroup.mk' (OuterAutomorphisms.inner (matrixProjectiveDerived Q))).comp
    (matrixProjectiveConjugationHom Q)

theorem matrixOuterAction_apply (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) :
    matrixOuterAction Q g =
      QuotientGroup.mk (matrixProjectiveConjugationHom Q g) := rfl

@[expose] def matrixImageOuterHom (Q : QuadraticForm K (Fin d → K)) :
    matrixProjectiveImage Q →* OuterAutomorphisms.Outer (matrixProjectiveDerived Q) :=
  (QuotientGroup.mk' (OuterAutomorphisms.inner (matrixProjectiveDerived Q))).domRestrict
    (matrixProjectiveImage Q)

theorem matrixImageOuterHom_apply (Q : QuadraticForm K (Fin d → K))
    (alpha : matrixProjectiveImage Q) :
    matrixImageOuterHom Q alpha = QuotientGroup.mk alpha.val := rfl

@[expose] def matrixImageInner (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (matrixProjectiveImage Q) :=
  (OuterAutomorphisms.inner (matrixProjectiveDerived Q)).subgroupOf (matrixProjectiveImage Q)

theorem mem_matrixImageInner_iff (Q : QuadraticForm K (Fin d → K))
    (alpha : matrixProjectiveImage Q) :
    alpha ∈ matrixImageInner Q ↔
      alpha.val ∈ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := Iff.rfl

instance matrixImageInner_normal (Q : QuadraticForm K (Fin d → K)) :
    (matrixImageInner Q).Normal := by
  unfold matrixImageInner
  infer_instance

theorem matrixImageOuterHom_kernel (Q : QuadraticForm K (Fin d → K)) :
    (matrixImageOuterHom Q).ker = matrixImageInner Q := by
  rw [matrixImageOuterHom, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  rfl

theorem matrixImageOuterHom_comp_conjugation (Q : QuadraticForm K (Fin d → K)) :
    (matrixImageOuterHom Q).comp (matrixProjectiveConjugationHom Q).rangeRestrict =
      matrixOuterAction Q := rfl

theorem matrixImageOuterHom_range (Q : QuadraticForm K (Fin d → K)) :
    (matrixImageOuterHom Q).range = (matrixOuterAction Q).range := by
  ext outerClass
  constructor
  · rintro ⟨⟨alpha, halpha⟩, rfl⟩
    obtain ⟨g, rfl⟩ := halpha
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨(matrixProjectiveConjugationHom Q).rangeRestrict g, rfl⟩

abbrev MatrixImageInnerQuotient (Q : QuadraticForm K (Fin d → K)) :=
  matrixProjectiveImage Q ⧸ matrixImageInner Q

@[expose] def matrixImageInnerProjection (Q : QuadraticForm K (Fin d → K)) :
    matrixProjectiveImage Q →* MatrixImageInnerQuotient Q := QuotientGroup.mk' _

@[expose] def matrixImageInnerQuotientEquiv (Q : QuadraticForm K (Fin d → K)) :
    MatrixImageInnerQuotient Q ≃* (matrixOuterAction Q).range :=
  ((QuotientGroup.quotientMulEquivOfEq (matrixImageOuterHom_kernel Q).symm).trans
    (QuotientGroup.quotientKerEquivRange (matrixImageOuterHom Q))).trans
      (MulEquiv.subgroupCongr (matrixImageOuterHom_range Q))

theorem matrixImageInnerQuotientEquiv_mk (Q : QuadraticForm K (Fin d → K))
    (alpha : matrixProjectiveImage Q) :
    (matrixImageInnerQuotientEquiv Q (matrixImageInnerProjection Q alpha)).val =
      matrixImageOuterHom Q alpha := rfl

theorem matrixImageInnerQuotientEquiv_symm_image (Q : QuadraticForm K (Fin d → K))
    (alpha : matrixProjectiveImage Q) :
    (matrixImageInnerQuotientEquiv Q).symm
      ⟨matrixImageOuterHom Q alpha,
        (matrixImageOuterHom_range Q).le ⟨alpha, rfl⟩⟩ =
      matrixImageInnerProjection Q alpha := by
  apply (matrixImageInnerQuotientEquiv Q).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (matrixImageInnerQuotientEquiv_mk Q alpha).symm

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImage
