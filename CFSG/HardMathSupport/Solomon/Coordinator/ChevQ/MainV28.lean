module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV24
public import CFSG.HardMathSupport.Dickson.Bal207.Holds
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest2
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighUnitaryGUTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


theorem i271ChevQ_of_inputs_v28 (hres : SeitzExcOpenRest3.SeitzExcOpenResidual3)
    (hD4 : OuterHigh2.SeitzGoodOuterHighD4Three) (hE6 : OuterHigh.SeitzGoodOuterHighE6Three)
    (hOut4 : ChevQOuterFour) : I271ChevQ :=
  i271ChevQ_of_inputs_v24
      (SeitzExcOpenRest2.seitzGoodInnerExcOpenRest_of_rest2
          (SeitzExcOpenRest3.seitzGoodInnerExcOpenRest2_of_residual3 hres))
      ⟨OuterHigh2.seitzGoodOuterHighUnitaryInndiag_holds, hD4⟩ hE6
      CFSG.HardMathSupport.Dickson.Bal207.bal207Corr_holds hOut4

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
