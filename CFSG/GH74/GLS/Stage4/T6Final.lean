module

public import CFSG.GH74.GLS.Stage4.T6Rle
public import CFSG.GH74.GLS.Stage4.T6SylM

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2

theorem t6_Syl (h11b : IVK_11_1b_nat) : T6SylProp := by
  intro G _ _ N u p h hΩ y R hTS hRle P₀ hP₀F hP₀p hP₀c
  have hR := t6RFacts_of h11b h hTS hRle
  obtain ⟨m, hm⟩ := h.q₁_pow
  obtain ⟨n, hn⟩ := h.q₂_pow
  exact Pst_sylow h hR hΩ hm hn hP₀F hP₀p hP₀c

theorem ch6T2Sec6'_proved (h11b : IVK_11_1b_nat) : Ch6T2Sec6' :=
  ch6T2Sec6'_of_leaves h11b t6_Rle (t6_Syl h11b)

end CFSG.GH74.GLS.Stage4.Rest.T6
