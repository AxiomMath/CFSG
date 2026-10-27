module

public import CFSG.ClassicalInvolution.Q3.Q3RSmallUpgrade
public import CFSG.ClassicalInvolution.Q3.Q3RSectionalFour

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution

theorem coreStep3_of_gh74 (hGH : GH74SectionalModels) (hE : ClassicalMemberParametersE7TwE6)
    (hNL : SectionalFourNonLie3) (hlarge : CoreStep3Large) : CoreStep3 :=
  coreStep3_of_E7_twistedE6 hE (citSectionalFour3_of_gh74_nonLie hGH hNL) hlarge

end CFSG.ClassicalInvolution.Q3
