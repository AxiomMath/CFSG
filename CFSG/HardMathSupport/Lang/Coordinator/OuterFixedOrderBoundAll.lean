module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSuzuki
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderLargeRee
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTriality
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSp
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaOdd
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaEven
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE7
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE8
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedF4
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

theorem outerFixedOrderBoundAt_Tits : OuterFixedOrderBoundAt .Tits :=
  fun _ _ _ _ _ _ _ _ ht => absurd rfl ht

theorem outerFixedOrderBound_of_trialityThree (h3 : OuterFixedOrderTrialityThree) :
    CFSG.AGLEmbedding.OuterSylow.OuterFixedOrderBound :=
  outerFixedOrderBound_of_forall fun t => by
    cases t with
    | PSL => exact UnitaryAutomorphisms.outerFixedOrderBoundAt_PSL
    | PSU => exact outerFixedOrderBoundAt_PSU
    | PSp => exact UnitaryAutomorphisms.outerFixedOrderBoundAt_PSp
    | POmegaOdd => exact UnitaryAutomorphisms.outerFixedOrderBoundAt_POmegaOdd
    | POmegaPlus => exact UnitaryAutomorphisms.outerFixedOrderBoundAt_POmegaPlus
    | POmegaMinus => exact UnitaryAutomorphisms.outerFixedOrderBoundAt_POmegaMinus
    | G2 => exact E6Descent.outerFixedOrderBoundAt_G2
    | F4 => exact E6Descent.outerFixedOrderBoundAt_F4
    | E6 => exact outerFixedOrderBoundAt_E6
    | E7 => exact E6Descent.outerFixedOrderBoundAt_E7
    | E8 => exact E6Descent.outerFixedOrderBoundAt_E8
    | twistedE6 => exact outerFixedOrderBoundAt_twistedE6
    | trialityD4 => exact outerFixedOrderBoundAt_trialityD4_of_three h3
    | twistedB2 => exact outerFixedOrderBoundAt_twistedB2
    | twistedG2 => exact outerFixedOrderBoundAt_twistedG2
    | twistedF4 => exact outerFixedOrderBoundAt_twistedF4
    | Tits => exact outerFixedOrderBoundAt_Tits

end CFSG.HardMathSupport.Lang.Coordinator
