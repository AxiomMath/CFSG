module

public import CFSG.GH74.GLS.C3.Layer1.St1P41Cls
public import CFSG.GH74.AS16.E2.Pump2Tables
public import CFSG.GH74.KGroups.TwoM12Fixed

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpCalc

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
open CFSG.GH74.E2 (Shape2M12 Shape2Sz8 K0Shape)

theorem rank4Tables_proved
    
    (hG : CFSG.GH74.Generic.GenericKnownFacts) (hF : CFSG.GH74.E2.E2ComponentFacts) : Rank4Tables where
  c2shape := fun L _ _ hC hP => c2Shape_of_inC2 hG hF hC hP
  k0fixed := fun K _ _ hK α hα2 hα1 L hL hq =>
    (CFSG.GH74.AS16.E2.pumpUpData2).shape_of_fixed K hK α hα2 hα1 L hL hq
  fixed60 := fun K _ _ h α hα2 hα1 L hL hq =>
    CFSG.GH74.KGroups.TwoM12.card_quasisimple_fixed_of_shape2M12 h α hα2 hα1 L hL hq
  noBoth := fun K _ _ h1 h2 => by
    have hc1 : Nat.card (K ⧸ center K) = 2 ^ 6 * 3 ^ 3 * 5 * 11 := card_of_isSporadic_M12 h1.2.2
    have hc2 : Nat.card (K ⧸ center K) = 29120 := by
      rw [card_of_lieModel_twistedB2 h2.2.2]
      decide
    omega

end CFSG.GH74.GLS.C3.Layer1.PumpCalc
