module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.T1515Stage

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def SixFiveNoE9_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Ce15Six T Mc M 5 →
      ¬ ∃ E : Subgroup (MulAut ↥(V154 T Mc M)),
        E ≤ autOn M (V154 T Mc M) ∧ IsElemAbelian 3 E ∧ Nat.card E = 9

end CFSG.Quasithin
