module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV50
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralD4Defs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E7NonToralHolds
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBlocks
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralD4Core
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeHyperNeg
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseIProof
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseIRankOne
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseIRankTwo
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseITau
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3CaseI
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCycNonA2
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoRankTwo
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Pairs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8NegCLines
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest5Even

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

set_option linter.unusedSectionVars false

section Residual


theorem seitzExcOpenResidual16_of_e8 (hS1 : E8NonToral.E8ThreeKilledPlaneBlocks)
    (hD4 : E8NonToral.E8NonToralD4Core) : SeitzExcOpenResidual16 :=
  ⟨KSE8NegC.e8NegCLineRest_of_twE6OpenDiag
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest5.twE6ThreeOpenDiag_holds,
    E6ThreeF4Close.f4NonToralNegHyperplane_holds, E6ThreeInner.twE6CaseIFrameH0_of_inputs
        CFSG.LieType.SeitzGeneration.ExcWideThree.e6CaseITable_holds E6ThreeInner.twE6CaseI_tau
        E6ThreeInner.twE6CaseI_rankOne_kind3A2 E6ThreeInner.twE6CaseI_rankOne_kind2A2
        E6ThreeInner.twE6CaseI_rankTwo,
    E6ThreeInner.twE6CaseIICycNonA2_holds, E6ThreeInner.twE6CaseIIRankTwo_of_pairs
        LieType.SeitzGeneration.ExcWideThree.e6Order3Pairs_holds,
    NonToralCore.e7NonToralTwoRest_holds,
    threeNonToralCubeRest_E8_of_normalizes (E8NonToral.e8NonToralNormalizes_of_core hS1 hD4)⟩

end Residual

section I271


theorem i271ChevQ_of_e8 (hS1 : E8NonToral.E8ThreeKilledPlaneBlocks)
    (hD4 : E8NonToral.E8NonToralD4Core) : I271ChevQ :=
  i271ChevQ_of_inputs_v50 (seitzExcOpenResidual16_of_e8 hS1 hD4) E6Three.KSGen.d5_fixedSpinPerfect

end I271

section Closing


theorem i271ChevQ_holds : I271ChevQ :=
  i271ChevQ_of_e8 E8NonToral.e8ThreeKilledPlaneBlocks_holds
    E8NonToral.e8NonToralD4Core_holds

end Closing

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
