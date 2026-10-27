module

public import CFSG.GH74.GLS.C3.Layer1.EvenStd
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseISyl

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

theorem b_thm2_terminal_standard_of_PU4 (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (hPU4 : B_cor_PU4) : B_thm2_terminal_standard := by
  intro G _ _ hG x y K T S h hterm
  obtain ⟨-, hshape⟩ := h.centerless_and_shape hG hL34 h102
  have hP : 2 ≤ pRank 2 ↥(T ⊓ K) := by
    obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hshape
    have := C3.Layer1.Back.pRank_mono' hU.1
    rw [pRank_of_isFourSub hU] at this
    exact this
  have hK : 2 ≤ pRank 2 ↥K := le_trans hP (C3.Layer1.Back.pRank_mono' inf_le_right)
  exact hPU4 G hG.kproper x K h.orderOf_x h.comp hK hterm

end CFSG.GH74.GLS
