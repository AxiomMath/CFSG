module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.S153DInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def Input15323_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → ¬ IsLnTwoQuot L 3

end CFSG.Quasithin
