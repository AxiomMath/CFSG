module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.S152Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace S152N

variable {T H : Subgroup G} {V A : Subgroup G}

@[expose] def Input15209Order_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ A ∈ deltaSet H (V154 T Mc M),
      (A ⊓ pCoreOf 2 H).relIndex A = 2

end S152N

end CFSG.Quasithin
