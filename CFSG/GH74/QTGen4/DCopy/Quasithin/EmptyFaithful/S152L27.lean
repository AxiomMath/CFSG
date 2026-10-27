module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.S152Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def StageLemma15227Two_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    V154 T Mc M ≤ pCoreOf 2 Mc

end CFSG.Quasithin
