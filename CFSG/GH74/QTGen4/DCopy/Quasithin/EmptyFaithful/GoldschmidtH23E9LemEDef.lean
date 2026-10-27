module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9Ctx
public import CFSG.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped Pointwise commutatorElement

@[expose] def Lemma15121E9_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    E9Ctx T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15121Concl Mc Z₁ L

end CFSG.Quasithin.E9
