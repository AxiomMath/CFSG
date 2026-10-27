module

public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Main
public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Fin

public section

namespace CFSG.GH74.GLS

theorem b_thm2_p89_J2_proved
    (hG : CFSG.GH74.Generic.GenericKnownFacts) (hF : CFSG.GH74.E2.E2ComponentFacts) :
    B_thm2_p89_J2 :=
  b_thm2_p89_J2_of (C3.Layer1.Bk.B810.b_p810_J2_proved hG hF)

end CFSG.GH74.GLS
