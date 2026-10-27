module

public import CFSG.GH74.Generic.S1.Exo.NbReduce
public import CFSG.GH74.Generic.S1.Exo.NbSingle

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74

theorem nbhdNoCommon_proved
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts) : NbhdNoCommon :=
  fun _ _ _ _ _ _ _ _ h => h.noCommon hG hF

end CFSG.GH74.Generic.S1.Exo
