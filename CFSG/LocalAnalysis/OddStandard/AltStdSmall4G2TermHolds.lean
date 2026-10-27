module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Psi

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

theorem g2Terminal_holds :
    G2Terminal := by
  intro G _ _ L Q n θ z c m A h ht
  have hm2 := h.two_le
  rcases (show m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with rfl | rfl | hm4
  · exact false_of_two c h ht
  · rcases expo_eq_four_or_eight L n z with h4 | h8
    · have hD := termData_DU c h ht
      exact hD.false_of_lt c (hD.sylow_of_char c (hD.char_of_three_le c le_rfl))
        (by rw [h4]; norm_num)
    · exact false_of_three c h ht h8
  · have hD := termData_DU c h ht
    refine hD.false_of_lt c (hD.sylow_of_char c (hD.char_of_three_le c (by omega))) ?_
    have h16 : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
    rcases expo_eq_four_or_eight L n z with he | he <;> rw [he] <;> norm_num at h16 ⊢ <;> omega

end CFSG.OddStandard.AltStdSmall4.G2
