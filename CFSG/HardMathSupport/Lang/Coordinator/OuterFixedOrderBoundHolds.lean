module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundAll
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2Char
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality3Char
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllMain
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddRot

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.HardMathSupport.Lang.E6Descent

theorem outerFixedOrderTrialityThree_holds : OuterFixedOrderTrialityThree :=
  outerFixedOrderTrialityThree_of_chars outerFixedOrderTrialityThreeChar_two
    outerFixedOrderTrialityThreeChar_three (outerFixedOrder_odd_of_rotLang rotLang_holds)

theorem outerFixedOrderBound_holds : CFSG.AGLEmbedding.OuterSylow.OuterFixedOrderBound :=
  outerFixedOrderBound_of_trialityThree outerFixedOrderTrialityThree_holds

end CFSG.HardMathSupport.Lang.Coordinator
