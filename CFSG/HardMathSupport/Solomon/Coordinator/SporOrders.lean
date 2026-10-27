module

public import CFSG.Open.MonsterY443Finiteness
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.HardMathSupport.Solomon.Proving.SporadicP2Table

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator


theorem sporadicOrdersTable_holds : SporadicOrdersTable := fun s =>
  (Nat.card_congr (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s).some.toEquiv).symm.trans
    (CFSG.AGLEmbedding.card_carrier_eq_sporOrd CFSG.Open.Open.monster_y443_derived_card s)

theorem sporadicP2Table_holds : SporadicP2Table :=
  CFSG.HardMathSupport.Solomon.Proving.sporadicP2Table_of_orders sporadicOrdersTable_holds

end CFSG.HardMathSupport.Solomon.Coordinator
