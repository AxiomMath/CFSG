module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsSp
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsPSL
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsPSU
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsE6
public import CFSG.ClassicalInvolution.Q3.Q3PlanTags

public section

namespace CFSG.ClassicalInvolution.Q3

@[expose] def ClassicalMemberParametersRest3 : Prop :=
  ClassicalMemberParameters3At .POmegaOdd ∧ ClassicalMemberParameters3At .POmegaPlus ∧
    ClassicalMemberParameters3At .POmegaMinus ∧ ClassicalMemberParameters3At .E7 ∧
    ClassicalMemberParameters3At .twistedE6 ∧ ClassicalMemberParameters3At .trialityD4

theorem classicalMemberParameters3_of_rest (h : ClassicalMemberParametersRest3) :
    ClassicalMemberParameters3 := by
  obtain ⟨hOdd, hPlus, hMinus, hE7, hE6t, hD4⟩ := h
  intro t ht
  rcases isFundTag_cases ht with hex | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact classicalMemberParameters3At_G2
    · exact classicalMemberParameters3At_F4
    · exact classicalMemberParameters3At_E6
    · exact hE7
    · exact classicalMemberParameters3At_E8
    · exact hE6t
    · exact hD4
  · exact classicalMemberParameters3At_PSL
  · exact classicalMemberParameters3At_PSp
  · exact classicalMemberParameters3At_PSU
  · exact hOdd
  · exact hPlus
  · exact hMinus

theorem smallUpgrade3_of_rest (hfund : ClassicalIsFundamental3)
    (h : ClassicalMemberParametersRest3) : SmallUpgrade3 :=
  smallUpgrade3_of_model hfund (classicalMemberParameters3_of_rest h)

end CFSG.ClassicalInvolution.Q3
