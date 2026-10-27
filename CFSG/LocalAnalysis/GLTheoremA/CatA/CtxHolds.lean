module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel


public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatDistinct

theorem ctx_holds
    :
    Ctx := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  · exact CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  · intro S _ d hd e
    exact CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hd e
  · obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    exact (Nat.card_congr e.toEquiv).symm.trans (by
      simpa using CFSG.Sporadic.Mathieu.card_M22)

end CFSG.LocalAnalysis.GLTheoremA.CatDistinct

