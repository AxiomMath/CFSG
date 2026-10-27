module

public import CFSG.HardMathSupport.Malle.SeitzCube.InnerExFrontier
public import CFSG.LieType.SeitzGeneration.ExcSeitzStatus
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.F4Phi3
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.E8Phi5
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Final

public section

namespace CFSG.LieType.SeitzGeneration

section Anisotropic


theorem seitzExcAnisotropicNotG2ThreePlus_holds :
    CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SeitzExcAnisotropicNotG2ThreePlus :=
  seitzExcAnisotropicNotG2ThreePlus_of_yardsticks
    ⟨CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.seitzExcAnisotropicF4Class_three,
      CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicF4Class_six⟩
    ⟨CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicE6Class_six,
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.seitzExcAnisotropicE8Class_five,
      CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicE8Class_ten,
      CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicE8Class_twelve⟩
    (CFSG.HardMathSupport.Seitz.TrialityEven.seitzExcAnisotropicTrialityEvenThree_of_leaves
      CFSG.HardMathSupport.Seitz.TrialityEven.trialityTwoThreePlanes_holds)

end Anisotropic

section InnerEx


theorem kFactSeitzRankTwoInnerEx_holds : KFactSeitzRankTwoInnerEx :=
  CFSG.HardMathSupport.Malle.SeitzCube.kFactSeitzRankTwoInnerEx_of_anisoN
    seitzExcAnisotropicNotG2ThreePlus_holds

end InnerEx

end CFSG.LieType.SeitzGeneration
