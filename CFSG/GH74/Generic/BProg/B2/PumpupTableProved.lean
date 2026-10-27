module

public import CFSG.GH74.Generic.BProg.B2.PumpupOpenProved
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2OutLieModel

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupOutOrders

open CFSG CFSG.GH74.GLS.Stage2.Bender.Thm1


theorem g2OuterFixedSimple_proved : G2OuterFixedSimple :=
  fun {_ _} hp hp2 hp3 hf {_} [_] [_] hY α hα hout =>
    g2_outer_involution_fixed_simple hp hp2 hp3 hf hY α hα hout

theorem pumpupOpen_proved : PumpupOpen :=
  pumpupOpen_of_g2 g2OuterFixedSimple_proved

theorem pumpupTableU_proved : PumpupTableU :=
  pumpupTableU_of_open pumpupOpen_proved

end CFSG.GH74.Generic.BProg.B2.PumpupOutOrders
