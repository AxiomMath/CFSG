module

public import CFSG.CGT.PushingUpLit.T2K.Inputs

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Assembly

@[expose] def Aschbacher78OneGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M : Subgroup G) (n : ℕ), T2Hyp G L M n →
    M ≤ Subgroup.normalizer (L : Set G) → ∀ T T' : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 2 T M → T' ≤ T →
      (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (blockU L : Set G)) ≤ T' →
        Subgroup.normalizer (T' : Set G) ≤ M ∨ CFSG.GH74.SectionalTwoRankLE G 4

theorem aschbacher78One_of_gen (h : Aschbacher78OneGen) : Aschbacher78One :=
  fun G _ _ L M n hn hLM T hT =>
    h G L M n hn hLM T T hT le_rfl (sup_le inf_le_left inf_le_left)

end CFSG.CGT.PushingUpLit.T2K
