module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

theorem exists_prime_primitive_dvd_pow_add_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 2 ≤ n) : ∃ r : ℕ, r.Prime ∧ r ≠ p ∧ r ≠ 2 ∧ r ∣ p ^ n + 1 ∧
      ∀ j : ℕ, 0 < j → j ≤ n + 1 → ¬ r ∣ p ^ j - 1 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨r, hr, hrd, hrmin⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3 (n := 2 * n) (by omega)
  have hpow : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.pos
  have hfac : p ^ (2 * n) - 1 = (p ^ n - 1) * (p ^ n + 1) := by
    have h1 : p ^ (2 * n) = p ^ n * p ^ n := by rw [two_mul, pow_add]
    rw [h1]
    zify [hpow, Nat.one_le_pow _ _ hp.pos, Nat.mul_le_mul hpow hpow]
    ring
  have hnot : ¬ r ∣ p ^ n - 1 := hrmin n (by omega) (by omega)
  have hrn : r ∣ p ^ n + 1 := by
    rw [hfac] at hrd
    exact (hr.dvd_mul.mp hrd).resolve_left hnot
  refine ⟨r, hr, ?_, ?_, hrn, fun j hj hjn => hrmin j hj (by omega)⟩
  · rintro rfl
    have h1 : r ∣ r ^ (2 * n) := dvd_pow_self r (by omega)
    have h2 : r ∣ r ^ (2 * n) - 1 := hrd
    have h3 : 1 ≤ r ^ (2 * n) := Nat.one_le_pow _ _ hp.pos
    have := (Nat.dvd_sub_iff_right h3 h1).mp h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · rintro rfl
    refine hrmin 1 (by omega) (by omega) ?_
    rw [pow_one]
    have hodd : Odd p := hp.odd_of_ne_two hp2
    exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one)
