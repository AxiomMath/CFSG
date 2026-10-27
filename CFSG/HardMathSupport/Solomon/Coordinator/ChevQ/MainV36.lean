module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV33
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Main
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Sel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Fixed
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.Bal209TwoFinal
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4OddMinus

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


theorem i271ChevQ_of_inputs_v36 (hres : SeitzExcOpenRest5.SeitzThreeResidual5 ∧
    SeitzExcOpenRest4.E8OneFiveCubeRest4 ∧ SeitzExcOpenRest3.E8TwoFiveCubeRest ∧
    SeitzExcOpenRest3.E8FourFiveCubeRest) (hE6 : SeitzE6ThreeRest) : I271ChevQ :=
  i271ChevQ_of_inputs_v33
      (SeitzExcOpenRest4.seitzExcOpenResidual3_of_residual4
          ⟨SeitzExcOpenRest5.seitzThreeResidual4_of_residual5 hres.1, hres.2⟩)
      OuterHighD4Odd.d4GraphA2FixIsoOdd_holds hE6
      ⟨KSFourU.bal209FourUAt_u6 CFSG.HardMathSupport.Dickson.Bal207.bal207Corr_holds,
          KSFourU.bal209FourUAt_of_inputs_loc KSFourU.e6FourUField KSFourU.e6Fixed
          (KSFourU.e6SelLoc KSU3Core.bal209FourUAt_u3)
          (KSFourU.fourUFixedSLOB_e6
              (bal209Two_of_bal207 CFSG.HardMathSupport.Dickson.Bal207.bal207Corr_holds))⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
