module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10OutFive
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6D4Outer
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6OutThree
public import CFSG.HardMathSupport.Timmesfeld.DFour.NonResidual44
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreDFour
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreAssembly
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator


theorem defCharInnerCoreFree_holds : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree :=
  CFSG.HardMathSupport.Timmesfeld.DefChar.defCharInnerCoreFree_of_dFour
    (CFSG.HardMathSupport.Timmesfeld.DefChar.defCharInnerCoreFreeFamDFour_of_image
      CFSG.HardMathSupport.Timmesfeld.DFour.dFourPrimeCentralizerInImage_holds)

theorem localTwoBalanceDefCharThree_holds : LocalTwoBalanceDefCharThree :=
  localTwoBalanceDefCharThree_of defCharOuterRankTwoThreeNonD4_proved defCharThreeD4Outer_proved
    defCharInnerCoreFree_holds

theorem localTwoBalanceDefCharFive_holds : LocalTwoBalanceDefCharFive :=
  localTwoBalanceDefCharFive_of defCharOuterRankTwoFive_proved defCharInnerCoreFree_holds

end CFSG.HardMathSupport.Solomon.Coordinator
