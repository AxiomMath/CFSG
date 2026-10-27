module

public import CFSG.Quasithin.EmptyFaithful.Gap6S1520
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152NTrans

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Input15209Exists_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∃ A : Subgroup G, IsMaxElemAbelian H A ∧
      ¬ A ≤ pCoreOf 2 H ∧ (A ⊓ pCoreOf 2 H).relIndex A = 2

theorem input15209Order_of_exists_F4 (h : Input15209Exists_F4) : S152N.Input15209Order_F4 :=
  fun G _ _ T Mc M hs H hH A hA =>
    Gap6.relIndex_eq_two_of_mem_deltaSet (h G T Mc M hs H hH) A hA

end CFSG.Quasithin
