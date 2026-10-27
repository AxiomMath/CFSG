module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthFive
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonalt
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldStd
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphEnd

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

theorem linearFieldRowInput_holds : LinearFieldRowInput := by
  rintro G _ _ L hset m f K _ _ hm hKc hf e t ht hKt F _ _ ι σ hσ1 hσσ hfix G₀ hG₀
    ⟨hLG₀, htG₀, hq, -, -, ψ, -, hψt⟩
  have hF : Nat.card F = 2 ^ (2 * f) := natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF
  exact false_of_globalField_of_card hset.standardSetting
    (isSolvable_outer_of_mulEquiv (by omega) e) (by omega) ι hσ1 hσσ hfix e ht hKt hG₀ hLG₀ htG₀
    hq ψ hψt

section Main

theorem seitzExclusion_highPSL_of_final_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : SLmNotOddLieInput) (hSpor : CatSLmSporadic) (hNorm : LinearSwapFactorNormalInput)
    (hFour : LinearFourInput) (hTwo : LinearTwoInput) : SeitzExclusion HighPSL :=
  seitzExclusion_highPSL_of_inputs hGLS hX hSpor linearFRInput_holds
    (fun _ h5 _ _ _ _ hKc _ => transvectionIntrinsicStd hKc (by omega)) linearFieldRowInput_holds
    linearSwapLiftInput_holds (linearSwapRowUniqueInput_of_factorNormal hNorm)
    linearOrthFiveInput_holds hFour hTwo

end Main

end CFSG.SeitzReduction.LinearPilot
