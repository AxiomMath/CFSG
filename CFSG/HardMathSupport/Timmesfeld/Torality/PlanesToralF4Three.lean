module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.HardMathSupport.Timmesfeld.Torality.F4Block
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharF4

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg


theorem planesToralBar_F4_three : PlanesToralBar Tag.F4 3 :=
  planesToralBar_three_of_block a2BlockToral_F4 fun _ _ a h3 =>
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three a h3).le

end CFSG.HardMathSupport.Timmesfeld.CrossChar
