module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoBigHolds
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoShape3
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoInnerLargeHolds
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoShapeTwoHolds
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ChainHolds
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerMain

public section

namespace CFSG.OddStandard.AltStdCycTwo


theorem altStdCyclicOddTwoFalse_of_tower (hW : AltStdSmall4.Tower.WrFalse)
    (hS : AltStdSmall4.Tower.SlFalse) :
    ComponentClassification.SolAltLit.AltStdCyclicOddTwoFalse :=
  altStdCyclicOddTwoFalse_of_parts cycTwoBigFalse_holds cycTwoShapeThreeFalse_holds
    cycTwoInnerLargeFalse_holds (AltStdSmall4.cycTwoInnerSmallFalse_of_tower hW hS)
    cycTwoShapeTwoLargeFalse_holds cycTwoShapeTwoElevenFalse_holds
    (AltStdSmall4.cycTwoShapeTwoNineFalse_of_tower hW hS)

theorem altStdCyclicOddTwoFalse_holds :
    ComponentClassification.SolAltLit.AltStdCyclicOddTwoFalse :=
  altStdCyclicOddTwoFalse_of_tower AltStdSmall4.Tower.wrFalse_holds
    AltStdSmall4.Tower.slFalse_holds

end CFSG.OddStandard.AltStdCycTwo
