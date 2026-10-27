module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

theorem e8Twelve_arith {p q : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (he : orderOf (q : ZMod p) = 12) :
    7 < p ∧ ¬ p ∣ q ∧ (q : ZMod p) ^ 4 - (q : ZMod p) ^ 2 + 1 = 0 ∧
      (p : ℤ) ∣ (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ : ∃ x : ZMod p, x = (q : ZMod p) := ⟨_, rfl⟩
  rw [← hx] at he ⊢
  have hx0 : x ≠ 0 := by
    intro h0
    have h1 := pow_orderOf_eq_one x
    rw [he, h0] at h1
    simp at h1
  have h12 : x ^ 12 = 1 := by simpa [he] using pow_orderOf_eq_one x
  have h6ne : x ^ 6 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [he]; norm_num)
  have h4ne : x ^ 4 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [he]; norm_num)
  have h6 : x ^ 6 + 1 = 0 := by
    have h : (x ^ 6 - 1) * (x ^ 6 + 1) = 0 := by linear_combination h12
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) h6ne
    · exact h
  have hx2 : x ^ 2 + 1 ≠ 0 := by
    intro h
    apply h4ne
    linear_combination (x ^ 2 - 1) * h
  have hΦ : x ^ 4 - x ^ 2 + 1 = 0 := by
    have h : (x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1) = 0 := by linear_combination h6
    exact (mul_eq_zero.1 h).resolve_left hx2
  have hdvd : 12 ∣ p - 1 := he ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have hp7' : 7 < p := by omega
  refine ⟨hp7', fun hdvd' => hx0 (hx ▸ (ZMod.natCast_eq_zero_iff q p).2 hdvd'), hΦ, ?_⟩
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_
  push_cast
  rw [← hx]
  exact hΦ

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
