module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Final

public section

namespace CFSG.GH74.GLS.Stage12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def S_stage4_G2_Std : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 → HasTwoThinConfiguration G →
    ∃ (Gs : Type) (_ : Group Gs), IsTwoCentralG2Type G Gs

theorem s_stage4_Std_of_branches (h6 : Stage1.Thm6.S_stage1_thm6_Std) (hg2 : S_stage4_G2_Std) :
    S_stage4_Std := by
  intro G _ _ hStd h3 hLB
  rcases hLB with h2 | ⟨_, hmeet⟩ | hT
  · omega
  · exact Or.inl (h6 G hStd h3 hmeet)
  · exact Or.inr (hg2 G hStd h3 hT)

end CFSG.GH74.GLS.Stage12
