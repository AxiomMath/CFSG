module

public import CFSG.LocalAnalysis.SectionRank.QTK.Basic

public section

namespace CFSG.SectionRank.QTK

theorem exists_odd_prime_dvd_of_ne_two_pow {m : ℕ} (hm : m ≠ 0) (h : ∀ a : ℕ, m ≠ 2 ^ a) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ m := by
  by_contra hcon
  push Not at hcon
  exact h _ (Nat.eq_prime_pow_of_unique_prime_dvd hm fun {d} hd hdm =>
    by_contra fun hd2 => hcon d hd hd2 hdm)

theorem exists_odd_prime_dvd_pred {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ¬ ∃ a : ℕ, p = 2 ^ a + 1) : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ p - 1 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  refine exists_odd_prime_dvd_of_ne_two_pow (by omega) fun a ha => h ⟨a, ?_⟩
  omega

theorem exists_odd_prime_dvd_succ {p : ℕ} (h : ¬ ∃ b : ℕ, p + 1 = 2 ^ b) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ p + 1 :=
  exists_odd_prime_dvd_of_ne_two_pow (by omega) fun b hb => h ⟨b, hb⟩

end CFSG.SectionRank.QTK
