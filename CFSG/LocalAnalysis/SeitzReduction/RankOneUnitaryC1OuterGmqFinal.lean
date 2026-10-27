module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmqCore
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmiCatHolds

public section

namespace CFSG.SeitzReduction.RankOne

theorem gmiCatSL2CoverInput_holds : GmiCatSL2CoverInput := by
  intro Y _ _ K hK hZp hZ p n _ _ hn h8 ⟨e⟩ T hT
  exact gmq_sl2_cover K hK hZp hZ p n hn h8 e T hT

end CFSG.SeitzReduction.RankOne
