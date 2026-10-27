module

public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThree
public import CFSG.HardMathSupport.Timmesfeld.Torality.PlanesToralF4Three
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7Three
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8Three

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem langToralPlane_F4_three : LangToralPlane Tag.F4 3 :=
  langToralPlane_F4_three_of_bar planesToralBar_F4_three

theorem langToralPlane_E7_three : LangToralPlane Tag.E7 3 :=
  langToralPlane_E7_three_of_bar planesToralBar_E7_three

theorem langToralPlane_E8_three : LangToralPlane Tag.E8 3 :=
  langToralPlane_E8_three_of_bar planesToralBar_E8_three

end CFSG.HardMathSupport.Timmesfeld.Torality
