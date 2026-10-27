module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownB
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2LeafRep
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2DownM
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.HardMathSupport.Solomon.Coordinator.YS08


theorem sporL3Down_B_holds
    : SporL3Down .B :=
  sporL3Down_of_inner CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    (CFSG.HardMathSupport.Dickson.Sec6.BM.sporL3DownInner_B_of_leaf
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      (HardMathSupport.Dickson.Sec6.BM.b3BLeaf_of_rep
          CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.bThreeB_seven_free))

theorem sporL3Down_M_holds
    : SporL3Down .M :=
  sporL3Down_of_inner CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.HardMathSupport.Dickson.Sec6.BM2.sporL3DownInner_M_holds

end CFSG.LocalAnalysis.GLTheoremA

end
