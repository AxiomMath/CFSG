module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false


theorem not_coprime_card_adjointG2_of_dvd_pow_six (k : Type) [Field k] [Finite k] {p : ℕ}
    (hp : p.Prime) (hd : p ∣ Nat.card k ^ 6 - 1) :
    ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.G2 k)) := by
  rw [← Nat.Prime.dvd_iff_not_coprime hp, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
  unfold CFSG.Open.ordG2
  exact Dvd.dvd.mul_right (dvd_mul_of_dvd_right hd _) _

theorem not_dvd_card_adjointG2 (k : Type) [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hpk : ¬ p ∣ Nat.card k) (hd : ¬ p ∣ Nat.card k ^ 6 - 1) :
    ¬ p ∣ Nat.card (adjointGroup Tag.G2 k) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
  unfold CFSG.Open.ordG2
  simp only [hp.dvd_mul]
  rintro ((h | h) | h)
  · exact hpk (hp.dvd_of_dvd_pow h)
  · exact hd h
  · exact hd (h.trans (sq_sub_one_dvd_pow_six_sub_one _))

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux
