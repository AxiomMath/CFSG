module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE8

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg


theorem planesToralBar_E8_three : PlanesToralBar Tag.E8 3 :=
  planesToralBar_three_of_block a2BlockToral_E8 fun _ _ a h3 =>
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_three a h3).le

end CFSG.HardMathSupport.Timmesfeld.CrossChar
