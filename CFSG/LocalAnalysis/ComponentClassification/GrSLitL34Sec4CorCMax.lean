module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrIsolatedFourEscape
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

theorem conjugate_eq_of_sup_eq {K : Subgroup X} {a : X} (h : K ⊔ conjugate K a = K) :
    conjugate K a = K :=
  eq_of_le_of_card_ge (le_sup_right.trans h.le)
    (card_map_of_injective (MulAut.conj a⁻¹).injective).ge

end CFSG.ComponentClassification.GSThmB.CorC
