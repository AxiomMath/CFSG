module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem nt1_neg_one_ne_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  intro h1
  apply hp2
  have h2 : (2 : ZMod p) = 0 := one_add_one_eq_two.symm.trans (neg_eq_iff_add_eq_zero.mp h1)
  have h4 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
  exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
    ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp h4)

theorem nt1_pow_eq_one_of_dvd {M : Type*} [Monoid M] {x : M} {d n : ℕ} (hd : x ^ d = 1)
    (h : d ∣ n) : x ^ n = 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [pow_mul, hd, one_pow]

theorem nt1_pow_eq_neg_one {p n : ℕ} [Fact p.Prime] (h : p ∣ 2 ^ n + 1) :
    (2 : ZMod p) ^ n = -1 := by
  have h0 : ((2 ^ n + 1 : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p _).mpr h
  push_cast at h0
  exact eq_neg_of_add_eq_zero_left h0

theorem nt1_pow_eq_one_of_dvd_sub {p a : ℕ} [Fact p.Prime] (h : p ∣ 2 ^ a - 1) :
    (2 : ZMod p) ^ a = 1 := by
  have h0 : ((2 ^ a - 1 : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p _).mpr h
  rw [Nat.cast_sub (Nat.one_le_two_pow : 1 ≤ 2 ^ a)] at h0
  push_cast at h0
  exact sub_eq_zero.mp h0

theorem nt1_odd_contra {p n a : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hneg : (2 : ZMod p) ^ n = -1)
    (ha : Odd a) (h : (2 : ZMod p) ^ a = 1) : False := by
  have h2n : (2 : ZMod p) ^ (2 * n) = 1 := by
    rw [pow_mul', hneg]
    exact neg_one_sq
  have hg : (2 : ZMod p) ^ Nat.gcd a (2 * n) = 1 := pow_gcd_eq_one.mpr ⟨h, h2n⟩
  have hdodd : Odd (Nat.gcd a (2 * n)) := Odd.of_dvd_nat ha (Nat.gcd_dvd_left a (2 * n))
  have hdn : Nat.gcd a (2 * n) ∣ n :=
    Nat.Coprime.dvd_of_dvd_mul_left (Odd.coprime_two_right hdodd) (Nat.gcd_dvd_right a (2 * n))
  have h1 : (2 : ZMod p) ^ n = 1 := nt1_pow_eq_one_of_dvd hg hdn
  exact nt1_neg_one_ne_one hp2 (hneg.symm.trans h1)

theorem nt1_even_contra {p n m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : Even n) (hm : Odd m)
    (hneg : (2 : ZMod p) ^ n = -1) (h : (2 : ZMod p) ^ (2 * m) = 1) : False := by
  have h2n : (2 : ZMod p) ^ (2 * n) = 1 := by
    rw [pow_mul', hneg]
    exact neg_one_sq
  have hg : (2 : ZMod p) ^ (2 * Nat.gcd m n) = 1 := by
    have h3 := pow_gcd_eq_one.mpr ⟨h, h2n⟩
    rwa [Nat.gcd_mul_left] at h3
  have hgodd : Odd (Nat.gcd m n) := Odd.of_dvd_nat hm (Nat.gcd_dvd_left m n)
  have h2g : 2 * Nat.gcd m n ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.symm (Odd.coprime_two_right hgodd))
      (even_iff_two_dvd.mp hn) (Nat.gcd_dvd_right m n)
  have h1 : (2 : ZMod p) ^ n = 1 := nt1_pow_eq_one_of_dvd hg h2g
  exact nt1_neg_one_ne_one hp2 (hneg.symm.trans h1)

theorem not_dvd_of_even_odd {n m p : ℕ} (hn : Even n) (hm : Odd m) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ 2 ^ n + 1) : ¬ p ∣ (2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1) := by
  haveI := Fact.mk hp
  intro h2
  have hneg := nt1_pow_eq_neg_one h
  have h3m : Odd (3 * m) := Odd.mul ⟨1, by norm_num⟩ hm
  rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
  · exact nt1_even_contra hp2 hn hm hneg (nt1_pow_eq_one_of_dvd_sub h3)
  · exact (nt1_odd_contra hp2 hneg h3m (nt1_pow_eq_one_of_dvd_sub h3)).elim

theorem dvd_two_pow_add_one_of {n m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 2 ^ n + 1)
    (hm : Odd m) (h2 : p ∣ (2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1)) : p ∣ 2 ^ m + 1 := by
  haveI := Fact.mk hp
  have hneg := nt1_pow_eq_neg_one h
  have h3m : Odd (3 * m) := Odd.mul ⟨1, by norm_num⟩ hm
  rcases (Nat.Prime.dvd_mul hp).mp h2 with h4 | h4
  · have h5 : (2 : ZMod p) ^ (2 * m) = 1 := nt1_pow_eq_one_of_dvd_sub h4
    rw [pow_mul'] at h5
    have h6 : ((2 : ZMod p) ^ m - 1) * ((2 : ZMod p) ^ m + 1) = 0 := by
      linear_combination h5
    rcases mul_eq_zero.mp h6 with h7 | h7
    · exact (nt1_odd_contra hp2 hneg hm (sub_eq_zero.mp h7)).elim
    · apply (CharP.cast_eq_zero_iff (ZMod p) p _).mp
      push_cast
      exact h7
  · exact (nt1_odd_contra hp2 hneg h3m (nt1_pow_eq_one_of_dvd_sub h4)).elim

end CFSG.LocalAnalysis.RankThreeUC.S15
