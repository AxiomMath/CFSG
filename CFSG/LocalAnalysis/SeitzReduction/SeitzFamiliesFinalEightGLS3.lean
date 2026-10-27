module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalEight
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveClAssembly
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FivePSUInner
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FivePSUGraph45
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExInFinal
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExInF4
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenFinal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenPSpMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevComm
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExInD4
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineJTwoCert
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineJTwoKind
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineLFourRank

public section

namespace CFSG.SeitzReduction

section SmallKind

theorem lFiveSmallKindRankInput_holds : LinearPilot.LFiveSmallKindRankInput :=
  LinearPilot.lFiveSmallKindRankInput_of_remaining LinearPilot.lFiveSevenPSp47Input_holds
    (fun _ _ => RankOne.excTwoPartInput_F4_all (by norm_num) (by norm_num) (by norm_num))
    (fun _ => RankOne.e7InnerTwoPartInput (by norm_num) (by norm_num) (by norm_num))
    (fun _ => RankOne.twistedE6InnerTwoPartInput (by norm_num) (by norm_num) (by norm_num))
    (RankOne.trialityInnerTwoPartInput (by norm_num) (by norm_num) (by norm_num))

end SmallKind

section OmegaPlusFour

theorem linearTwoSwapRowAtInput_six_of_final8_gls3
    (hlab6 : LinearPilot.LinearTwoSwapLabelDualAtInput 6) : LinearPilot.LinearTwoSwapRowAtInput 6 :=
  linearTwoSwapRowAtInput_six_of_final8 gls3OddLieAutComponentsInput hlab6

end OmegaPlusFour

section Two

section Omega

theorem seitzExclusion_highPOmegaPlus_holds : SeitzExclusion HighPOmegaPlus :=
  seitzExclusion_highPOmegaPlus_of_final8 gls3OddLieAutComponentsInput

theorem seitzExclusion_highPOmegaMinus_holds : SeitzExclusion HighPOmegaMinus :=
  seitzExclusion_highPOmegaMinus_of_final8 gls3OddLieAutComponentsInput

section StarPrime

theorem starPrimeStatement_holds {f : ℕ} (hf : 2 ≤ f) : RankOne.StarPrimeStatement f :=
  RankOne.starPrime_of_gls3_of_classical gls3OddLieAutComponentsInput
    RankOne.oddFivePSUInnerInput_holds RankOne.oddFiveU45GraphInput_holds
    RankOne.oddFiveSL2BoundFamilyInput_PSp_holds RankOne.oddFiveSL2BoundFamilyInput_POmegaOdd_holds
    RankOne.oddFiveSL2BoundFamilyInput_POmegaPlus_holds
    RankOne.oddFiveSL2BoundFamilyInput_POmegaMinus_holds hf

section RankOne

theorem seitzRankOneExclusion_of_final8_gls3 (hswap : RankOne.U3C1OuterMuOneSwapInput) :
    SeitzRankOneExclusion :=
  seitzRankOneExclusion_of_starPrime_norm (fun _ hf => starPrimeStatement_holds hf) hswap

end RankOne

end StarPrime

section PSp

section LFive

theorem linearTwoSwapRowAtInput_five_of_final8_gls3 (hsyl5 : LinearPilot.LFiveSOneSylowPartInput)
    (hlab5 : LinearPilot.LinearTwoSwapLabelDualAtInput 5) : LinearPilot.LinearTwoSwapRowAtInput 5 :=
  linearTwoSwapRowAtInput_five_of_final8 gls3OddLieAutComponentsInput hsyl5 hlab5

section PSL

theorem linearTwoFiveSixInput_of_final8_gls3 (hF5 : LinearPilot.LinearTwoFieldKindAtInput 5)
    (hsyl5 : LinearPilot.LFiveSOneSylowPartInput)
    (hlab5 : LinearPilot.LinearTwoSwapLabelDualAtInput 5)
    (hlab6 : LinearPilot.LinearTwoSwapLabelDualAtInput 6) :
    LinearPilot.LinearTwoFiveSixInput :=
  LinearPilot.linearTwoFiveSixInput_of_at_six gls3OddLieAutComponentsInput
    LinearPilot.catSLmSporadicAt_three (LinearPilot.catSLmSporadicAt_of_four_le le_rfl) hF5
    (linearTwoSwapRowAtInput_five_of_final8_gls3 hsyl5 hlab5)
    (SporadicRefine.linearTwoSmallKindAtInput_five_of_sylow lFiveSmallKindRankInput_holds
        SporadicRefine.j2SylowSupportInput_of_cert)
    (linearTwoSwapRowAtInput_six_of_final8_gls3 hlab6)
    (LinearPilot.linearTwoSmallKindAtInput_six_of_rank SporadicRefine.sixSmallKindRankInput)

end PSL

end LFive

end PSp

end Omega

end Two

end CFSG.SeitzReduction
