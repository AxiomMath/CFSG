module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

@[expose] def Residual44 {K : Type} [Field K] (gh : matrixDerived (coordinateQuadPlus 4 K)) :
    Prop :=
  ∀ w : Fin (2 * 4) → K,
    (((matrixLinearEquiv gh.val : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)) - 1) ^ 2 :
      Module.End K (Fin (2 * 4) → K)) w = 0 → coordinateQuadPlus 4 K w = 0

end CFSG.HardMathSupport.Timmesfeld.DFour
