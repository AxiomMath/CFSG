module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

open Orbit

@[expose] def AltNaturalCoverSeven_F4 : Prop :=
  ∀ (V : Type) [CommGroup V] [CFSG.GH74.QTGen4.Finite4 V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (Z : Subgroup V), Z ≤ fixV H → commV H = ⊤ →
      AlternatingNatural H ⊤ Z 7 → Z = ⊥

end CFSG.Quasithin.H13
