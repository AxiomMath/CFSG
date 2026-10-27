module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.S146Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Stage146BranchACore_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    (∃ H : Subgroup G, IsHTM T M H ∧ ¬ OddCoreModTwoTrivial H) → FinalData146Core T M

end CFSG.Quasithin
