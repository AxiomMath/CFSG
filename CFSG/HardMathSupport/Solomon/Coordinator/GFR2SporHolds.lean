module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporRest
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem gapFinalPumpup_of_open16 (hR : ∀ name ∈ restNames, SporNoPumpup name)
    (hb : LieOrderBridge) (h1 : LieDownChev) (h2 : LieNoHatSix) : GapFinalPumpup :=
  gapFinalPumpup_of_rest
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
    sporadicOrdersTable_holds CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group hR hb h1 h2

end CFSG.HardMathSupport.Solomon.Coordinator
