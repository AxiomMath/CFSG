module

public import CFSG.GH74.GLS.C3.Layer1.St1Leaves
public import CFSG.GH74.GLS.C3.Layer1.Split

public section

namespace CFSG.GH74.GLS

theorem isEvenType_of_thm6_thm7 {G : Type} [Group G] (h7 : St1Thm7 G) (h6 : St1Thm6 G)
    (hr : 3 ≤ pRank 2 G) : IsEvenType G :=
  ⟨h7, h6, hr⟩

theorem isEvenType_of_leaves (h7 : B_st1_thm7) (h41 : B_st1_prop41) (h51 : B_st1_prop51)
    (h4 : B_st1_thm4) (h5 : B_st1_thm5) (h6 : B_st1_thm6) {G : Type} [Group G] [Finite G]
    (hG : C3Hyp G) (hN : NoU2Triple G) : IsEvenType G := by
  have T7 := h7 G hG hN
  have P41 := h41 G hG hN T7
  have P51 := h51 G hG hN T7 P41
  have T4 := h4 G hG hN T7 P41 P51
  have T5 := h5 G hG hN T7 P41 T4
  have T6 := h6 G hG hN T7 P41 P51 T5
  exact isEvenType_of_thm6_thm7 T7 T6 (by rw [hG.pRank_eq_four]; norm_num)

theorem s_stage1_rank4_of_leaves (h7 : B_st1_thm7) (h41 : B_st1_prop41) (h51 : B_st1_prop51)
    (h4 : B_st1_thm4) (h5 : B_st1_thm5) (h6 : B_st1_thm6) : S_stage1_rank4 := by
  intro G _ _ hG
  by_cases hU : ∃ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K
  · exact Or.inr hU
  · exact Or.inl (isEvenType_of_leaves h7 h41 h51 h4 h5 h6 hG hU)

end CFSG.GH74.GLS
