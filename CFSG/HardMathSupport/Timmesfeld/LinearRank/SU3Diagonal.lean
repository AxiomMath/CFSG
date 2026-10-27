module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.UnitaryDiagonal
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.SU3Main

public section

namespace CFSG.HardMathSupport.Timmesfeld.LinearRank

open CFSG.HardMathSupport.Timmesfeld.FieldBonus

theorem su3DiagonalRank : SU3DiagonalRank := by
  intro f K _ h hf hf3 H hHD hH hc
  have := h.finite
  have hle := card_le_of_diagonal (n := 3) h le_rfl (not_three_two_of_three_le hf3)
    Nat.prime_three (by norm_num) (three_dvd_two_pow_add_one hf) H hHD hH
  rw [hc] at hle
  norm_num at hle

end CFSG.HardMathSupport.Timmesfeld.LinearRank
