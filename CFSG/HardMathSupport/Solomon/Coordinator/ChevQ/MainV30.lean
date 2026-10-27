module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV28
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Three2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


theorem i271ChevQ_of_inputs_v30 (hres : SeitzExcOpenRest3.SeitzExcOpenResidual3)
    (hG : OuterHigh3.D4GraphA2FixedPlanes ∧
        OuterHigh3.D4GraphG2SylowPairNonsplit) (hE6 : OuterHigh.SeitzGoodOuterHighE6Three)
    (hOut4 : ChevQOuterFour) : I271ChevQ :=
  i271ChevQ_of_inputs_v28 hres
      (OuterHigh3.seitzGoodOuterHighD4Three_of_graphCubes
          CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          (OuterHigh3.d4ThreeGraphCubes_of_residuals
              CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds hG.1 hG.2)) hE6 hOut4

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
