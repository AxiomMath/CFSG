module

public import CFSG.GH74.GLS.Prop27.LocBalAll
public import CFSG.GH74.KGroups.M12LocBal

public section

namespace CFSG.GH74.GLS.Prop27

open CFSG.GH74.E2 CFSG.Blueprint

theorem locBal2_M12
    : LocBal2 fun S _ => NativeSporadic.IsSporadic S .M12 :=
  fun X _ _ N hN hS hC e he => KGroups.M12.locBal2_M12 X N hN hS hC e he

theorem Prop27LocalBalance.of_Sz8
    (hSz8 : LocBal2 ShapeSz8) : Prop27LocalBalance :=
  Prop27LocalBalance.of_M12_Sz8 locBal2_M12 hSz8

theorem s_prop27G_of_Sz8
    (hG : Generic.GenericKnownFacts) (hF : E2ComponentFacts)
    (hT : S_Thm182_P27) (hSz8 : LocBal2 ShapeSz8) : S_prop27G :=
  s_prop27G_of_M12_Sz8 hG hF hT locBal2_M12 hSz8

end CFSG.GH74.GLS.Prop27
