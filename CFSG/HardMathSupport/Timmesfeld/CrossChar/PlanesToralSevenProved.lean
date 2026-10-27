module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralSevenE
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.A6ChainTabE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.A6ChainTabE8
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.SevenCharE7
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.SevenCharE8
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.FiveCharE8

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.KE

section Trans

theorem a6ChainTransitive_E7 : A6ChainTransitive Tag.E7 a6chainE7 := by
  intro β hβ
  obtain ⟨v, hv⟩ := exists_weyl_a6chain_E7 hβ
  refine ⟨v, fun k => ?_⟩
  rw [← hv k]
  congr 1

theorem a6ChainTransitive_E8 : A6ChainTransitive Tag.E8 a6chainE8 := by
  intro β hβ
  obtain ⟨v, hv⟩ := exists_weyl_a6chain_E8 hβ
  refine ⟨v, fun k => ?_⟩
  rw [← hv k]
  congr 1

end Trans

section E7

theorem planesToralBar_E7_seven : Torality.PlanesToralBar Tag.E7 7 :=
  planesToralBar_E7_seven_of_stab a6ChainTransitive_E7 fun _ _ a ha =>
    (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_seven a ha).le

end E7

section E8

theorem planesToralBar_E8_seven :
    Torality.PlanesToralBar Tag.E8 7 :=
  planesToralBar_E8_seven_of_stab a6ChainTransitive_E8 fun _ _ a ha =>
    (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_seven a ha).le

theorem planesToralBar_E8_five :
    Torality.PlanesToralBar Tag.E8 5 :=
  planesToralBar_E8_five_of_stab fun _ _ a ha =>
    (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five a ha).le

theorem e8FiveToralPlane_proved : E8FiveToralPlane :=
  e8FiveToralPlane_of_stab fun _ _ a ha =>
    (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five a ha).le

end E8

end CFSG.HardMathSupport.Timmesfeld.CrossChar
