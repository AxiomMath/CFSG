module

public import CFSG.GH74.Generic.BProg.B2.PumpupOutOrders
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutMain

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupOutOrders

open CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Certified


theorem psp4OuterNoShape_proved : Psp4OuterNoShape :=
  fun {_ _} hp hp2 hf {_} [_] [_] hY α hα hout L hL Z hZc hZo hZn hsh =>
    psp4_outer_involution_noShape hp hp2 hf hY α hα hout L hL ⟨Z, hZc, hZo, hZn, hsh⟩

theorem pumpupOpen_of_g2 (hg2 : G2OuterFixedSimple) : PumpupOpen :=
  pumpupOpen_of_simple hg2 psp4OuterNoShape_proved

end Certified

end CFSG.GH74.Generic.BProg.B2.PumpupOutOrders
