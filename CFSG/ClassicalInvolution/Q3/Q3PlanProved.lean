module

public import CFSG.ClassicalInvolution.Q3.Q3PlanFundPSp
public import CFSG.ClassicalInvolution.Q3.Q3PlanFundPSU
public import CFSG.ClassicalInvolution.Q3.Q3PlanFundOrth
public import CFSG.ClassicalInvolution.Q3.Q3ExcG2
public import CFSG.ClassicalInvolution.Q3.Q3ExcF4
public import CFSG.ClassicalInvolution.Q3.Q3ExcE7
public import CFSG.ClassicalInvolution.Q3.Q3ExcE8
public import CFSG.ClassicalInvolution.Q3.Q3ExcTwE6
public import CFSG.ClassicalInvolution.Q3.Q3ExcTwD4

public section

namespace CFSG.ClassicalInvolution.Q3

theorem classicalIsFundamental3_proved : ClassicalIsFundamental3 :=
  classicalIsFundamental3_of_tags
    (fun t ht => by
      rcases isFundTag_cases ht with h | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact classicalMembersFundamental3Tag_G2
        · exact classicalMembersFundamental3Tag_F4
        · exact classicalMembersFundamental3Tag_E6
        · exact classicalMembersFundamental3Tag_E7
        · exact classicalMembersFundamental3Tag_E8
        · exact classicalMembersFundamental3Tag_twistedE6
        · exact classicalMembersFundamental3Tag_trialityD4
      · exact classicalMembersFundamental3Tag_PSL
      · exact classicalMembersFundamental3Tag_PSp
      · exact classicalMembersFundamental3Tag_PSU
      · exact classicalMembersFundamental3Tag_POmegaOdd
      · exact classicalMembersFundamental3Tag_POmegaPlus
      · exact classicalMembersFundamental3Tag_POmegaMinus)
    (fun t _ hex => by
      rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact oddCentralizerFreeTag_G2
      · exact oddCentralizerFreeTag_F4
      · exact oddCentralizerFreeTag_E6
      · exact oddCentralizerFreeTag_E7
      · exact oddCentralizerFreeTag_E8
      · exact oddCentralizerFreeTag_twistedE6
      · exact oddCentralizerFreeTag_trialityD4)

end CFSG.ClassicalInvolution.Q3
