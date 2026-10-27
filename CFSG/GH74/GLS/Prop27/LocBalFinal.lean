module

public import CFSG.GH74.GLS.Prop27.LocBalM12
public import CFSG.GH74.GLS.Prop27.LocBalSuzuki

public section

namespace CFSG.GH74.GLS.Prop27

open CFSG.GH74.E2

theorem prop27LocalBalance :
    Prop27LocalBalance :=
  Prop27LocalBalance.of_Sz8 locBal2_Sz8_bender

theorem s_prop27G_of_facts
    (hG : Generic.GenericKnownFacts) (hF : E2ComponentFacts)
    (hT : S_Thm182_P27) : S_prop27G :=
  s_prop27G_of_Sz8 hG hF hT locBal2_Sz8_bender

end CFSG.GH74.GLS.Prop27
