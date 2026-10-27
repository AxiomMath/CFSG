module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.EmptyFaithful.S152Defs

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def StageLemma15226One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∃ hV : IsElemAbelian 2 (V154 T Mc M),
      1 < E3.rParam (V154 T Mc M) ∧ 1 < E3.sParam hV

end CFSG.Quasithin
