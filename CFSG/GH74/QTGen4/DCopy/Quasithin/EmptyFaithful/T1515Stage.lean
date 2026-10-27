module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.T1515Stage

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def StageTheorem1515_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → ¬ Ce15 T Mc M

end CFSG.Quasithin
