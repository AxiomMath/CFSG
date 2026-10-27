module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightTrialityFamily
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightTrialityTorus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightBoundsPlus

public section

namespace CFSG.SeitzReduction.OmegaPilot

theorem plusFourTrialityInput_holds : PlusFourTrialityInput := fun F _ _ _ =>
  ⟨plusFourTriality F, plusFourTriality_pow_three, plusFourTriality_smul_pointFamily_ne,
    plusFourTriality_mul_fieldAutHom, symmetryAut_conj_plusFourTriality,
    permutesNodeTori_plusFourTriality⟩

theorem omegaPlusFourAutNormalFormInput_holds : OmegaPlusFourAutNormalFormInput :=
  omegaPlusFourAutNormalFormInput_of_triality plusFourTrialityInput_holds

theorem omegaPlusFourEndInput_holds : OmegaPlusFourEndInput :=
  omegaPlusFourEndInput_of_triality plusFourTrialityInput_holds

theorem omegaPlusFourUniqueInput_holds : OmegaPlusFourUniqueInput :=
  omegaPlusFourUniqueInput_of_triality omegaPlusLinearInvolutionInput_four
    plusFourTrialityInput_holds

end CFSG.SeitzReduction.OmegaPilot
