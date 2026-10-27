module

public import CFSG.GH74.Generic.S1.Exo.Q3HFinal
public import CFSG.GH74.Generic.S1.Exo.Q3Single

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74

theorem q3H_proved
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts) : Q3H :=
  q3H_of_inputs rankTwoStmt_proved fun _ _ _ _ _ _ _ h => nbhd3_no_common hG hF h

end CFSG.GH74.Generic.S1.Exo
