module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV37
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2Conj
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeRest
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwA2Conj
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnerLine
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadCubeGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadSinger
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveFourMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveToral

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzExcOpenResidual7 : Prop :=
  SeitzExcOpenRest6.SeitzThreeResidual6 ∧ KSE8Five.E8OneFiveNonToralGriess ∧ KSE8Five.E8TwoFiveNonToral

@[expose] def SeitzE6ThreeFive : Prop :=
  E6Three.E6ThreeCompGen ∧ E6Three.E6ThreeNotAll24NFA ∧ E6Three.E6ThreeNotAll24NFB2 ∧ E6Three.TwE6ThreeCompGen ∧
    E6Three.TwE6NotAll24Gen

theorem seitzExcOpenResidual6_of_residual7 (hres : SeitzExcOpenResidual7) : SeitzExcOpenResidual6 :=
  ⟨hres.1, KSE8Five.e8OneFiveCubeRest4_of_nonToral hres.2.1, KSE8Five.e8TwoFiveCubeRest_of_nonToral hres.2.2,
    KSE8Five.e8FourFiveCubeRest_holds⟩

theorem seitzE6ThreeRest_of_e6ThreeFive (h : SeitzE6ThreeFive) : SeitzE6ThreeRest :=
  OuterHigh.seitzE6ThreeRest_of_nonPar
      (E6Three.e6DiagNonParCubes_of_core kFactSeitzRankTwo_holds E6Three.e6ThreeA2Conj_holds
          E6Three.e6ThreeLayerGen_holds E6Three.e6ThreeTorusGen_holds h.1
          (E6Three.e6ThreeNotAll24Gen_of_nf E6Three.e6ThreeLayerGen_holds
              (E6Three.e6ThreeNotAll24NF_of_parts h.2.1 E6Three.e6ThreeNotAll24NFB1_holds h.2.2.1)))
      (E6Three.twE6DiagNonParCubes_of_core kFactSeitzRankTwo_holds E6Three.twE6ThreeA2LineStmt_holds
          E6Three.twE6ThreeA2Conj_holds E6Three.twE6ThreeLayerGen_holds
          E6Three.twE6ThreeTorusGen_holds h.2.2.2.1 h.2.2.2.2)

theorem i271ChevQ_of_inputs_v38 (hres : SeitzExcOpenResidual7) (hE6 : SeitzE6ThreeFive) : I271ChevQ :=
  i271ChevQ_of_inputs_v37 (seitzExcOpenResidual6_of_residual7 hres) (seitzE6ThreeRest_of_e6ThreeFive hE6)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
