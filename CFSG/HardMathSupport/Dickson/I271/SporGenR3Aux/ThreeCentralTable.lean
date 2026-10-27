module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith

public section

namespace CFSG.HardMathSupport.Dickson.I271.ThreeCentralTable

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem three_dvd_exceptional {t : StatedLieTag} {n p f : ℕ}
    (h : 3 ∣ (exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) :
    (t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ p = 3 ∧ f = 1) ∨
    (t = .G2 ∧ n = 0 ∧ p = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1) := by
  revert h
  unfold exceptionalOrders
  split
  all_goals intro h
  all_goals first
    | (exfalso; revert h; norm_num; done)
    | simp

theorem three_dvd_generic {t : StatedLieTag} {n p f : ℕ}
    (h : 3 ∣ (genericOrders t n p f).1) :
    (t = .PSL ∧ 3 ∣ Nat.gcd n (p ^ f - 1)) ∨ (t = .PSU ∧ 3 ∣ Nat.gcd n (p ^ f + 1)) ∨
    (t = .E6 ∧ 3 ∣ p ^ f - 1) ∨ (t = .twistedE6 ∧ 3 ∣ p ^ f + 1) := by
  cases t <;> simp only [genericOrders] at h <;> (try split_ifs at h)
  all_goals first
    | exact Or.inl ⟨rfl, h⟩
    | exact Or.inr (Or.inl ⟨rfl, h⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨rfl, h.trans (Nat.gcd_dvd_right _ _)⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨rfl, h.trans (Nat.gcd_dvd_right _ _)⟩))
    | (exfalso; revert h; norm_num; done)
    | (exfalso; have := h.trans (Nat.gcd_dvd_left _ _); omega)

theorem three_dvd_table_cases {t : StatedLieTag} {n p f : ℕ}
    (h : 3 ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2)) :
    (t = .PSL ∧ 3 ∣ Nat.gcd n (p ^ f - 1)) ∨ (t = .PSU ∧ 3 ∣ Nat.gcd n (p ^ f + 1)) ∨
    (t = .E6 ∧ 3 ∣ p ^ f - 1) ∨ (t = .twistedE6 ∧ 3 ∣ p ^ f + 1) ∨
    (t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ p = 3 ∧ f = 1) ∨
    (t = .G2 ∧ n = 0 ∧ p = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1) := by
  obtain ⟨hb1, hb2⟩ := genericOrders_snd_le t n p f
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · rcases three_dvd_generic h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exfalso
      have := Nat.le_of_dvd hb1 h
      omega
  · rcases three_dvd_exceptional h with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

end CFSG.HardMathSupport.Dickson.I271.ThreeCentralTable
