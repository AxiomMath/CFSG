module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TrialityThree
public import CFSG.LieType.SeitzGeneration.ExcSeitzStatus

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.AGLEmbedding CFSG.LieType.SeitzGeneration CFSG.Yardstones.M0a200c08cf60


theorem kFactSeitzOuterCubeRankTwo_of_open (h4 : ExcAnisotropicF4Residuals)
    (h5 : ExcAnisotropicE6E8Residuals) (hOdd : TrialityOuterCubesThreeOdd) :
    KFactSeitzOuterCubeRankTwo :=
  kFactSeitzOuterCubeRankTwo_of_excRest
    (kFactSeitzOuterCubeRankTwoExcRest_of_anisotropic_odd
      (seitzExcAnisotropic_of_yardsticks h4 h5
        (CFSG.HardMathSupport.Seitz.TrialityEven.seitzExcAnisotropicTrialityEvenThree_of_leaves
          CFSG.HardMathSupport.Seitz.TrialityEven.trialityTwoThreePlanes_holds))
      hOdd)

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
