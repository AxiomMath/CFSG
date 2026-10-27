
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.Sporadic.J4.QT2LocRadGen
public import CFSG.Sporadic.J4.QTOutLinGen

@[expose] public section

namespace CFSG.QuasithinUnique.A5.Dec2

open CFSG.QuasithinUnique.A5 CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem prime_dvd_cases {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : r ∣ 501397585920) : r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 11 ∨ r = 23 := by
  have h0 : r ∣ 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 * 23 := by
    have : (501397585920 : ℕ) = 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 * 23 := by norm_num
    rwa [this] at h
  rcases (Nat.Prime.dvd_mul hr).1 h0 with h0 | h0
  · rcases (Nat.Prime.dvd_mul hr).1 h0 with h0 | h0
    · rcases (Nat.Prime.dvd_mul hr).1 h0 with h0 | h0
      · rcases (Nat.Prime.dvd_mul hr).1 h0 with h0 | h0
        · rcases (Nat.Prime.dvd_mul hr).1 h0 with h0 | h0
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
              (hr.dvd_of_dvd_pow h0)) hr2
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
              (hr.dvd_of_dvd_pow h0))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h0))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h0)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1
        h0))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h0))))

theorem pow_dvd_bound (r k : ℕ) (hk : ¬ r ^ (k + 1) ∣ 501397585920) {a : ℕ}
    (ha : r ^ a ∣ 501397585920) : a ≤ k := by
  by_contra h
  exact hk ((pow_dvd_pow r (by omega : k + 1 ≤ a)).trans ha)

theorem factorization_cases {r : ℕ} (hr : r.Prime) {n : ℕ} (hn : n ≠ 0) (hrn : r ∣ n)
    (hdvd : n ∣ 501397585920) (k : ℕ) (hk : ¬ r ^ (k + 1) ∣ 501397585920) :
    1 ≤ n.factorization r ∧ n.factorization r ≤ k := by
  refine ⟨(hr.dvd_iff_one_le_factorization hn).1 hrn, ?_⟩
  have h1 : r ^ n.factorization r ∣ n := Nat.ordProj_dvd n r
  exact pow_dvd_bound r k hk (h1.trans hdvd)

end CFSG.QuasithinUnique.A5.Dec2
