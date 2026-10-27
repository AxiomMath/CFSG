module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV38
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


theorem seitz2310CubeSimple_of_v38 (hres : ChevQ.SeitzExcOpenResidual7) (hE6 : ChevQ.SeitzE6ThreeFive) :
    ChevQ.Seitz2310CubeSimple := by
  have h6 : ChevQ.SeitzExcOpenResidual6 :=
    ⟨hres.1, ChevQ.KSE8Five.e8OneFiveCubeRest4_of_nonToral hres.2.1,
      ChevQ.KSE8Five.e8TwoFiveCubeRest_of_nonToral hres.2.2, ChevQ.KSE8Five.e8FourFiveCubeRest_holds⟩
  have h4 : ChevQ.SeitzExcOpenRest4.SeitzExcOpenResidual4 :=
    ⟨ChevQ.SeitzExcOpenRest5.seitzThreeResidual4_of_residual5
      (ChevQ.SeitzExcOpenRest6.seitzThreeResidual5_of_residual6 h6.1), h6.2⟩
  have hEo : ChevQ.SeitzExcOpenRest.SeitzGoodInnerExcOpenRest :=
    ChevQ.SeitzExcOpenRest2.seitzGoodInnerExcOpenRest_of_rest2
      (ChevQ.SeitzExcOpenRest3.seitzGoodInnerExcOpenRest2_of_residual3
        (ChevQ.SeitzExcOpenRest4.seitzExcOpenResidual3_of_residual4 h4))
  have hD4 : ChevQ.OuterHigh2.SeitzGoodOuterHighD4Three :=
    ChevQ.OuterHigh3.seitzGoodOuterHighD4Three_of_graphCubes kFactSeitzRankTwo_holds
      (ChevQ.OuterHigh3.d4ThreeGraphCubes_of_residuals kFactSeitzRankTwo_holds
        (ChevQ.OuterHigh3.d4GraphA2FixedPlanes_of_fixIsoOdd kFactSeitzRankTwo_holds
          ChevQ.OuterHighD4Odd.d4GraphA2FixIsoOdd_holds)
        ChevQ.OuterHigh3.d4GraphG2SylowPairNonsplit_holds)
  exact InputsSeitz3.seitz2310CubeSimple_of_v23 hEo
    (ChevQ.OuterHigh2.seitzGoodOuterHighClassicalDiag_of_inndiag kFactSeitzRankTwo_holds
      ChevQ.OuterHigh2.seitzGoodOuterHighUnitaryInndiag_holds hD4)
    (ChevQ.OuterHigh.seitzE6ThreeRest_of_nonPar
        (ChevQ.E6Three.e6DiagNonParCubes_of_core kFactSeitzRankTwo_holds
            ChevQ.E6Three.e6ThreeA2Conj_holds ChevQ.E6Three.e6ThreeLayerGen_holds
            ChevQ.E6Three.e6ThreeTorusGen_holds hE6.1
            (ChevQ.E6Three.e6ThreeNotAll24Gen_of_nf ChevQ.E6Three.e6ThreeLayerGen_holds
                (ChevQ.E6Three.e6ThreeNotAll24NF_of_parts hE6.2.1
                    ChevQ.E6Three.e6ThreeNotAll24NFB1_holds hE6.2.2.1)))
        (ChevQ.E6Three.twE6DiagNonParCubes_of_core kFactSeitzRankTwo_holds
            ChevQ.E6Three.twE6ThreeA2LineStmt_holds ChevQ.E6Three.twE6ThreeA2Conj_holds
            ChevQ.E6Three.twE6ThreeLayerGen_holds ChevQ.E6Three.twE6ThreeTorusGen_holds hE6.2.2.2.1
            hE6.2.2.2.2)).1

@[expose] def SeitzLowRest4 : Prop :=
  QuasiHigh5.SeitzCoverFamExcRest2Rest ∧ QuasiHigh4.SeitzCoverCubeRest4 ∧ ChevQ.SeitzExcOpenResidual7 ∧
    ChevQ.SeitzE6ThreeFive

theorem seitzLowRest3_of_rest4 (h : SeitzLowRest4) : SeitzRest.SeitzLowRest3 :=
  ⟨h.1, h.2.1, seitz2310CubeSimple_of_v38 h.2.2.1 h.2.2.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge

end
