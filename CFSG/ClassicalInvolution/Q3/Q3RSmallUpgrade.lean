module

public import CFSG.ClassicalInvolution.Q3.Q3RParamTwD4
public import CFSG.ClassicalInvolution.Q3.Q3RCoreStepPieces
public import CFSG.ClassicalInvolution.Q3.Q3PlanProved
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsAllExc

public section

namespace CFSG.ClassicalInvolution.Q3

@[expose] def ClassicalMemberParametersE7TwE6 : Prop :=
  ClassicalMemberParameters3At .E7 ∧ ClassicalMemberParameters3At .twistedE6

theorem classicalMemberParameters3_of_E7_twistedE6 (h : ClassicalMemberParametersE7TwE6) :
    ClassicalMemberParameters3 :=
  classicalMemberParameters3_of_exc ⟨h.1, h.2, classicalMemberParameters3At_trialityD4⟩

theorem smallUpgrade3_of_E7_twistedE6 (h : ClassicalMemberParametersE7TwE6) : SmallUpgrade3 :=
  smallUpgrade3_of_model classicalIsFundamental3_proved
    (classicalMemberParameters3_of_E7_twistedE6 h)

theorem coreStep3_of_E7_twistedE6 (h : ClassicalMemberParametersE7TwE6)
    (hs4 : CITSectionalFour3) (hlarge : CoreStep3Large) : CoreStep3 :=
  coreStep3_of_pieces (smallUpgrade3_of_E7_twistedE6 h) hs4 hlarge

end CFSG.ClassicalInvolution.Q3
