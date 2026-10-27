module

public import CFSG.HardMathSupport.Dickson.Sec6.Assembly
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Final
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Spor
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownB
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2LeafRep
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2DownM
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fi24
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LieRestAll
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResComplete
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6Real
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadMain
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTwMain
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Wire
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThNo93
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.NoOrderSixtyFiveM

public section

namespace CFSG.HardMathSupport.Dickson.Sec6


theorem sec6Out_of_open
    (h09 : CFSG.Yardstones.M67c2c3e09a6b.I271OpenFamilies) :
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6Out :=
  sec6Out_of_remaining
    (up34SporLeaf_of_rest
      ⟨sporL34Free_of_down (CFSG.HardMathSupport.Solomon.Coordinator.YS08.sporL3DownInner_Fi24
          CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group),
        sporL34Free_of_down (BM.sporL3DownInner_B_of_leaf
          CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group (BM.b3BLeaf_of_rep
              CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.bThreeB_seven_free)),
        sporL34Free_of_down BM2.sporL3DownInner_M_holds⟩)
    up34Chev2Leaf_holds h09 I1431.noOrder65_M
    I1431.noOrder93_Th
    (I1431.i1431LieRest_of_open I1431.OrthL2.d4RootSL2_holds
      (I1431.y1431_lieRest_u6Real
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput)
      I1431.y1431_noCfg_e6Bad I1431.y1431_noCfg_twE6Bad I1431.excResidual_f4_proved
      I1431.excResidual_e6Good_proved I1431.excResidual_twE6Good_proved
      I1431.excResidual_e7_proved I1431.excResidual_e8_proved)
    I1431.OrthL2.d4RootSL2_holds

end CFSG.HardMathSupport.Dickson.Sec6
