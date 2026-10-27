module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFinal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFourSwapUnique

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

theorem linearSwapFactorNormalFourInput_of_factorNormal (hN : LinearSwapFactorNormalInput) :
    LinearSwapFactorNormalFourInput :=
  fun G _ _ L hset f K _ _ _ hKc hf e t ht hKt => hN G L hset 3 f K le_rfl hKc hf e t ht hKt

section Main

theorem linearFourInput_of_final_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : SLmNotOddLieInput) (hSpor : CatSLmSporadic) (hNorm : LinearSwapFactorNormalInput) :
    LinearFourInput :=
  linearFourInput_of_factorNormal hGLS (hX 3 le_rfl) (hSpor 3 le_rfl)
    (linearSwapFactorNormalFourInput_of_factorNormal hNorm)

theorem seitzExclusion_highPSL_of_final_inputs_four (hGLS : GLS3OddLieAutComponentsInput)
    (hX : SLmNotOddLieInput) (hSpor : CatSLmSporadic) (hNorm : LinearSwapFactorNormalInput)
    (hTwo : LinearTwoInput) : SeitzExclusion HighPSL :=
  seitzExclusion_highPSL_of_final_inputs hGLS hX hSpor hNorm
    (linearFourInput_of_final_inputs hGLS hX hSpor hNorm) hTwo

end Main

end CFSG.SeitzReduction.LinearPilot
