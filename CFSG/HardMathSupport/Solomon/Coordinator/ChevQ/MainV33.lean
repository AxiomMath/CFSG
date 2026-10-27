module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV31
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Three3
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Three4

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


theorem i271ChevQ_of_inputs_v33 (hres : SeitzExcOpenRest3.SeitzExcOpenResidual3)
    (hA : OuterHigh3.D4GraphA2FixIsoOdd) (hE6 : SeitzE6ThreeRest) (h209 : Bal209FourUAt
        OuterFourInAux.IsU6EightIndex (OuterFourInAux.FieldAutU 6) ∧ Bal209FourUAt
        OuterFourInAux.IsTwE6EightIndex OuterFourInAux.FieldAutTwE6) : I271ChevQ :=
  i271ChevQ_of_inputs_v31 hres
      ⟨(OuterHigh3.d4GraphA2FixedPlanes_of_fixIsoOdd CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds hA),
          OuterHigh3.d4GraphG2SylowPairNonsplit_holds⟩ hE6 h209

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
