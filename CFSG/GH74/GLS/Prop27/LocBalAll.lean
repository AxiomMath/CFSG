module

public import CFSG.GH74.GLS.Prop27.Main
public import CFSG.GH74.GLS.Prop27.LocBalM11
public import CFSG.GH74.GLS.Prop27.LocBalL28
public import CFSG.GH74.GLS.Prop27.LocBalL33
public import CFSG.GH74.GLS.Prop27.LocBalU33

public section

namespace CFSG.GH74.GLS.Prop27

open CFSG.GH74.E2 CFSG.Blueprint

theorem Prop27LocalBalance.of_M12_Sz8
    (hM12 : LocBal2 fun S _ => NativeSporadic.IsSporadic S .M12) (hSz8 : LocBal2 ShapeSz8) :
    Prop27LocalBalance where
  L28 := locBal2_L28
  L33 := locBal2_L33
  U33 := locBal2_U33
  M11 := locBal2_M11
  M12 := hM12
  Sz8 := hSz8

theorem s_prop27G_of_M12_Sz8
    (hG : Generic.GenericKnownFacts) (hF : E2ComponentFacts)
    (hT : S_Thm182_P27) (hM12 : LocBal2 fun S _ => NativeSporadic.IsSporadic S .M12)
    (hSz8 : LocBal2 ShapeSz8) : S_prop27G :=
  s_prop27G_of_leaves ⟨hG, hF, hT, Prop27LocalBalance.of_M12_Sz8 hM12 hSz8⟩

end CFSG.GH74.GLS.Prop27
