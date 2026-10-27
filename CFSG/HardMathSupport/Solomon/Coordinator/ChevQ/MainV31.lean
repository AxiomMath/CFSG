module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV30
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzBal2
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzUE
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighUnitaryGUTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U3CoreMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzHyperGoodIn
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourIn
public import CFSG.HardMathSupport.Dickson.Bal207.Holds
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzE6ThreeRest : Prop :=
  OuterHigh.SeitzGoodOuterHighE6Three ∧ OuterFourSeitz.TwE6EightDiagCubes

theorem i271ChevQ_of_inputs_v31 (hres : SeitzExcOpenRest3.SeitzExcOpenResidual3)
    (hG : OuterHigh3.D4GraphA2FixedPlanes ∧
        OuterHigh3.D4GraphG2SylowPairNonsplit) (hE6 : SeitzE6ThreeRest) (h209 : Bal209FourUAt
        OuterFourInAux.IsU6EightIndex (OuterFourInAux.FieldAutU 6) ∧ Bal209FourUAt
        OuterFourInAux.IsTwE6EightIndex OuterFourInAux.FieldAutTwE6) : I271ChevQ := by
  have hEo := SeitzExcOpenRest.seitzGoodInnerExcOpen_of_rest seitzGoodInnerOrthTwo_holds
    (SeitzExcOpenRest2.seitzGoodInnerExcOpenRest_of_rest2 (SeitzExcOpenRest3.seitzGoodInnerExcOpenRest2_of_residual3 hres))
  have hL : SeitzHyperLie fun d p _ => SeitzGoodIndex p d.1 :=
    SeitzHyperGoodInAux.seitzHyperLie_good (seitzGoodInnerOrth_of_two seitzGoodInnerOrthTwo_holds)
      (seitzGoodInnerUnitary_of_nonDiag (seitzGoodInnerUnitaryNonDiag_of_nonabRest
        seitzGoodInnerUnitaryNonabRest))
      (SeitzHyperGoodInAux.seitzGoodInnerExcAll_of_top (seitzGoodInnerExc_of_open hEo))
  exact i271ChevQ_of_inputs_v30 hres hG hE6.1
    (chevQOuterFour_of_families kFactSeitzRankTwo_holds CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
      (OuterFourSeitz.seitz2310FourFreeAt_u6_of hL OuterHigh3.u6EightDiagCubes_holds)
      (OuterFourSeitz.seitz2310FourFreeAt_twE6_of hL hE6.2)
      (OuterFourSeitz.seitz2310FourFreeAt_d4_of hL (OuterFourSeitz.d4EightOuterCubes_of_graph kFactSeitzRankTwo_holds
        (OuterHigh3.d4EightGraphCubes_of_residuals kFactSeitzRankTwo_holds hG.1 hG.2)))
      KSU3Core.bal209FourUAt_u3 h209.1 h209.2 CFSG.HardMathSupport.Dickson.Bal207.bal207D4_holds
      (OuterFourSeitz.bal2010D4_of_graphComp CFSG.HardMathSupport.Dickson.Bal207.bal207Corr_holds
        OuterFourSeitz2.d4EightGraphComp_holds))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
