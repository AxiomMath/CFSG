module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImageBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImage

open CatalogueBOrthogonalSemilinear

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def matrixInnerQuotientAction (Q : QuadraticForm K (Fin d → K)) :
    similarityPairs Q →* MatrixImageInnerQuotient Q :=
  (matrixImageInnerProjection Q).comp (matrixProjectiveConjugationHom Q).rangeRestrict

theorem matrixInnerQuotientAction_apply (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) :
    matrixInnerQuotientAction Q g =
      QuotientGroup.mk ((matrixProjectiveConjugationHom Q).rangeRestrict g) := rfl

theorem matrixInnerQuotientAction_surjective (Q : QuadraticForm K (Fin d → K)) :
    Function.Surjective (matrixInnerQuotientAction Q) :=
  (QuotientGroup.mk'_surjective (matrixImageInner Q)).comp
    (MonoidHom.rangeRestrict_surjective (matrixProjectiveConjugationHom Q))

theorem matrixInnerQuotientAction_equiv (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) :
    (matrixImageInnerQuotientEquiv Q (matrixInnerQuotientAction Q g)).val =
      matrixOuterAction Q g := rfl

theorem matrixImageInnerQuotient_derivedSeries_iff (Q : QuadraticForm K (Fin d → K))
    (r : ℕ) :
    derivedSeries (MatrixImageInnerQuotient Q) r = ⊥ ↔
      derivedSeries (matrixOuterAction Q).range r = ⊥ := by
  have hmap := map_derivedSeries_eq
    (f := (matrixImageInnerQuotientEquiv Q).toMonoidHom)
    (matrixImageInnerQuotientEquiv Q).surjective r
  constructor
  · intro h
    rw [h, Subgroup.map_bot] at hmap
    exact hmap.symm
  · intro h
    apply (Subgroup.map_eq_bot_iff_of_injective _
      (f := (matrixImageInnerQuotientEquiv Q).toMonoidHom)
      (matrixImageInnerQuotientEquiv Q).injective).mp
    exact hmap.trans h

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImage
