module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE7

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg


theorem planesToralBar_E7_three : PlanesToralBar Tag.E7 3 :=
  planesToralBar_three_of_block a2BlockToral_E7 fun _ _ a h3 =>
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_three a h3).le

end CFSG.HardMathSupport.Timmesfeld.CrossChar
