module

public import CFSG.ClassicalInvolution.Q3.Q3EE7
public import CFSG.ClassicalInvolution.Q3.Q3ETwE6
public import CFSG.ClassicalInvolution.Q3.Q3RWiring

public section

namespace CFSG.ClassicalInvolution.Q3

theorem classicalMemberParametersE7TwE6_proved : ClassicalMemberParametersE7TwE6 :=
  ⟨classicalMemberParameters3At_E7, classicalMemberParameters3At_twistedE6⟩

theorem classicalMemberParameters3_proved : ClassicalMemberParameters3 :=
  classicalMemberParameters3_of_E7_twistedE6 classicalMemberParametersE7TwE6_proved

theorem smallUpgrade3_proved : SmallUpgrade3 :=
  smallUpgrade3_of_E7_twistedE6 classicalMemberParametersE7TwE6_proved

theorem coreStep3_of_gh74_proved (hGH : GH74SectionalModels) (hNL : SectionalFourNonLie3)
    (hlarge : CoreStep3Large) : CoreStep3 :=
  coreStep3_of_gh74 hGH classicalMemberParametersE7TwE6_proved hNL hlarge

end CFSG.ClassicalInvolution.Q3

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

theorem q3Inputs₅_of_residuals_proved (hGH : GH74SectionalModels) (hQ : QuasisimpleConnected3)
    (hNL : SectionalFourNonLie3) (hlarge : CoreStep3Large) : Q3Inputs₅ :=
  q3Inputs₅_of_residuals hGH hQ classicalMemberParametersE7TwE6_proved hNL hlarge

end CFSG.ClassicalInvolution.MilestoneAssembly
