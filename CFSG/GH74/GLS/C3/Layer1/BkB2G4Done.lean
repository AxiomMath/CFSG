module

public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Bridge
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Schreier
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Unbal
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Exc
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Filter.Lie.EvenSeries
public import CFSG.GH74.Filter.Lie.TitsElem
public import CFSG.GH74.Filter.Lie.TwistedD4Even
public import CFSG.GH74.Filter.Lie.TwistedE6Even
public import CFSG.GH74.Filter.Lie.TwistedF4
public import CFSG.GH74.Filter.Monster.Main
public import CFSG.GH74.Filter.Small.Exceptional
public import CFSG.GH74.Filter.Sporadic.All

public section

namespace CFSG.GH74.GLS

open CFSG CFSG.GH74 CFSG.GH74.Filter CFSG.GH74.GLS.C3.Layer1.Bk.B2G4

theorem b_B2_g4_proved
    : B_B2_g4 := by
  have hout : ∀ s ∈ sporadicOut, S_sporadic s := t_sporadic_all t_sporadic_M
  exact b_B2_g4_of_inputs (schreierG4_of_out hout)
    (unbalancedG4_of_checks
      (evenExceptionalCheckG4_of_filter t_G2_even t_F4_even t_E6_even t_E7_even t_E8_even t_2E6_even
        t_3D4_even)
      (largeReeTitsCheckG4_of_filter t_twistedF4 t_Tits) (sporadicNonJ1CheckG4_of_out hout))
    (exceptionalG4_of_out hout)

end CFSG.GH74.GLS
