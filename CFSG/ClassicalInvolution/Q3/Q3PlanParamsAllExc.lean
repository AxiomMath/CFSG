module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsAll
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsOrth

public section

namespace CFSG.ClassicalInvolution.Q3

theorem classicalMemberParametersRest3_of_exc (h : ClassicalMemberParameters3At .E7 ∧
    ClassicalMemberParameters3At .twistedE6 ∧ ClassicalMemberParameters3At .trialityD4) :
    ClassicalMemberParametersRest3 :=
  ⟨classicalMemberParameters3At_POmegaOdd, classicalMemberParameters3At_POmegaPlus,
    classicalMemberParameters3At_POmegaMinus, h.1, h.2.1, h.2.2⟩

theorem classicalMemberParameters3_of_exc (h : ClassicalMemberParameters3At .E7 ∧
    ClassicalMemberParameters3At .twistedE6 ∧ ClassicalMemberParameters3At .trialityD4) :
    ClassicalMemberParameters3 :=
  classicalMemberParameters3_of_rest (classicalMemberParametersRest3_of_exc h)

theorem smallUpgrade3_of_exc (hfund : ClassicalIsFundamental3)
    (h : ClassicalMemberParameters3At .E7 ∧ ClassicalMemberParameters3At .twistedE6 ∧
        ClassicalMemberParameters3At .trialityD4) : SmallUpgrade3 :=
  smallUpgrade3_of_rest hfund (classicalMemberParametersRest3_of_exc h)

end CFSG.ClassicalInvolution.Q3
