module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem index_eq_of_alternating {M : Subgroup X}
    (h7 : Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin 7))) :
    (pPrimeCore 2 M).index = 2520 := by
  obtain ⟨e7⟩ := h7
  rw [index_eq_card, Nat.card_congr e7.toEquiv, GSThmB.card_alternatingGroup_seven]

end CFSG.ComponentClassification.GSThmB.CorC
