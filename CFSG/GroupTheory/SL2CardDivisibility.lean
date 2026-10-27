module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.GroupTheory

open scoped MatrixGroups

theorem dvd_card_sl2_of_dvd_mul_sq_sub_one {F : Type} [Field F] [Finite F] {q r : ℕ}
    (hF : Nat.card F = q) (h : r ∣ q * (q ^ 2 - 1)) :
    r ∣ Nat.card (SL(2, F)) := by
  rw [CFSG.GorensteinWalter.sl2_card_formula, hF]
  exact h

theorem dvd_card_sl2_cube_of_dvd_mul_sq_sub_one {F : Type} [Field F] [Finite F] {q r : ℕ}
    (hF : Nat.card F = q ^ 3) (h : r ∣ q * (q ^ 2 - 1)) :
    r ∣ Nat.card (SL(2, F)) := by
  rw [CFSG.GorensteinWalter.sl2_card_formula, hF]
  refine h.trans (Nat.mul_dvd_mul (dvd_pow_self q (by norm_num : 3 ≠ 0)) ?_)
  have hpow : (q ^ 2) ^ 3 = (q ^ 3) ^ 2 := by ring
  have h1 : q ^ 2 - 1 ∣ (q ^ 3) ^ 2 - 1 := by
    have := Nat.sub_one_dvd_pow_sub_one (q ^ 2) 3
    rwa [hpow] at this
  exact h1

end CFSG.GroupTheory
