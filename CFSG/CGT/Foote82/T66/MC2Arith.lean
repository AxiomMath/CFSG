module

public import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCClimb

public section

namespace CFSG.CGT.Foote82

namespace MC2

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

theorem card_omegaMinusTwo_two : Nat.card ↥(omegaMinusTwo 2) = 25920 := by
  have h := card_omegaMinusTwo (k := 2) le_rfl
  have : (Nat.card ↥(omegaMinusTwo 2) : ℤ) = 25920 := by
    rw [h]
    decide
  exact_mod_cast this

theorem card_omegaMinusTwo_three : Nat.card ↥(omegaMinusTwo 3) = 197406720 := by
  have h := card_omegaMinusTwo (k := 3) (by norm_num)
  have : (Nat.card ↥(omegaMinusTwo 3) : ℤ) = 197406720 := by
    rw [h]
    decide
  exact_mod_cast this

theorem factorial_div_two_ne_omegaMinus_eight (n : ℕ) : n.factorial / 2 ≠ 197406720 := by
  rcases Nat.lt_or_ge n 12 with h | h
  · have h1 := Nat.factorial_le (show n ≤ 11 by omega)
    have h11 : Nat.factorial 11 = 39916800 := by decide
    omega
  · have h1 := Nat.factorial_le h
    have h12 : Nat.factorial 12 = 479001600 := by decide
    omega

theorem factorial_div_two_ne_card_omegaMinusTwo {m n : ℕ} (hm : m = 2 ∨ m = 3)
    (h : n.factorial / 2 = Nat.card ↥(omegaMinusTwo m)) : False := by
  rcases hm with rfl | rfl
  · rw [card_omegaMinusTwo_two] at h
    exact factorial_div_two_ne n h
  · rw [card_omegaMinusTwo_three] at h
    exact factorial_div_two_ne_omegaMinus_eight n h

end MC2

end CFSG.CGT.Foote82
