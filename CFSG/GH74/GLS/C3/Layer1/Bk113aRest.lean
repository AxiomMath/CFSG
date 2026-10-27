module

public import CFSG.GH74.GLS.C3.Layer1.Bk113aFive
public import CFSG.GH74.GLS.C3.Layer1.Bk113aSeven
public import CFSG.GH74.GLS.C3.Layer1.BkL113aTop

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open CFSG CFSG.GH74.GLS

theorem b_lemma113a_rest_of_leaves
    (h81 : B_iv2_8_1) (h92 : B_lemma92) : B_lemma113a_rest := by
  intro G _ _ hG x K L M T Q hh p91 _ hT hcases
  rcases hcases with h5 | ⟨h7, _⟩
  · obtain ⟨e5⟩ := h5
    exact lemma113a_five h81 h92 hG hh.a p91 e5 hT
  · obtain ⟨e7⟩ := h7
    exact lemma113a_A7L h81 h92 hG hh.a p91 e7 hT

end CFSG.GH74.GLS.C3.Layer1.Bk
