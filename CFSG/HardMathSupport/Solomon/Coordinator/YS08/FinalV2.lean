module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Char3Export
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownB
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Minus
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2LeafRep
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2DownM
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPF4Small

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.HardMathSupport.Solomon.Coordinator

set_option linter.unusedSectionVars false

theorem lThreeFourComponentFacts_of_rank4_only
    (h4 : LieComp.ExcRationalLieTypesOuterD_rank4) :
    CFSG.Yardstones.M67c2c3e09a6b.LThreeFourComponentFacts :=
  lThreeFourComponentFacts_of_residuals
    (CFSG.HardMathSupport.Dickson.Sec6.BM.sporL3DownInner_B_of_leaf
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group (Dickson.Sec6.BM.b3BLeaf_of_rep
          CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.bThreeB_seven_free))
    CFSG.HardMathSupport.Dickson.Sec6.BM2.sporL3DownInner_M_holds
    (LieComp.trialityOddA2Comps_of_toral LieComp.TriA2.a2PlusComps_holds
        LieComp.TriA2.a2MinusComps_holds)
    LieComp.d4Char3Outer_holds
    (LieComp.excChar3Export_of_outer YS08.LieQ.lieQConstrainedInner_three_holds
      LieComp.excChar3OuterExport_holds)
    (LieComp.excRationalLieTypesOuter_of_D (LieComp.excRationalLieTypesOuterD_of_rank4 h4))
    LieComp.excRationalLieTypesF4Two_holds

theorem lThreeFourComponentFacts_holds
    : CFSG.Yardstones.M67c2c3e09a6b.LThreeFourComponentFacts :=
  lThreeFourComponentFacts_of_rank4_only LieComp.excRationalLieTypesOuterD_rank4_holds

end CFSG.HardMathSupport.Solomon.Coordinator.YS08

end
