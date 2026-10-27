module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV17
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeOrthTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.LinearAutCubeProof
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryPow
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighExc
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz3D48Proof
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighDiag

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


theorem i271ChevQ_of_inputs_v24 (hEoRest : SeitzExcOpenRest.SeitzGoodInnerExcOpenRest)
    (hDiagRest : OuterHigh2.SeitzGoodOuterHighUnitaryInndiag ∧
        OuterHigh2.SeitzGoodOuterHighD4Three) (hE6 : OuterHigh.SeitzGoodOuterHighE6Three)
    (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr) (hOut4 : ChevQOuterFour) :
    I271ChevQ :=
  i271ChevQ_of_inputs_v17 CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
      seitzGoodInnerOrthTwo_holds seitzGoodInnerUnitaryNonabRest
      (SeitzExcOpenRest.seitzGoodInnerExcOpen_of_rest seitzGoodInnerOrthTwo_holds hEoRest)
      (OuterHigh.seitzGoodOuterHighClassical_of_diag
          CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          (OuterHigh2.seitzGoodOuterHighClassicalDiag_of_inndiag
              CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds hDiagRest.1 hDiagRest.2))
      (OuterHigh.seitzGoodOuterHighExceptional_of_e6Three
          CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds hE6)
      Seitz3D48Proof.seitz3D48Cube_holds LinearAutCubeProof.linearAutCube_holds
      Star2313UnitaryProof.star2313UnitaryInput_holds h207 hOut4

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
