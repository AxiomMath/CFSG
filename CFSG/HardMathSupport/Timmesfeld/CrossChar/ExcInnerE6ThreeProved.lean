module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE6ThreeLinesTwo
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ2

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LangTorus

set_option linter.unusedSectionVars false


theorem e6RootLineCommuteTwo_holds : E6RootLineCommuteTwo :=
  CFSG.HardMathSupport.Timmesfeld.LangTorus.e6RootLineCommuteTwo

theorem innerPlaneBalanceAt_E6_three_proved (hcp : LangComponentPieces) :
    InnerPlaneBalanceAt .E6 3 :=
  innerPlaneBalanceAt_E6_three_of_commuteTwo hcp e6RootLineCommuteTwo_holds

end CFSG.HardMathSupport.Timmesfeld.CrossChar
