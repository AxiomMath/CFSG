module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalGraph
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFinalFour

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

section Main

theorem seitzExclusion_highPSL_of_cat_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : SLmNotOddLieInput) (hSpor : CatSLmSporadic) (hTwo : LinearTwoInput) :
    SeitzExclusion HighPSL :=
  seitzExclusion_highPSL_of_final_inputs_four hGLS hX hSpor linearSwapFactorNormalInput_holds hTwo

end Main

end CFSG.SeitzReduction.LinearPilot
