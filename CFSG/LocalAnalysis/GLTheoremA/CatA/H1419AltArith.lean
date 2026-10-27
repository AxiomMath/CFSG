module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1419

open scoped Nat
open CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char (L3Order)

theorem factorial_two_emultiplicity {m n k Y : ℕ} (hk : 1 ≤ k) (h2n : 2 * n = m !)
    (h3 : 3 * n = 2 ^ (3 * k) * Y) (hY : Odd Y) : emultiplicity 2 (m !) = ((3 * k + 1 : ℕ) : ℕ∞) := by
  have hcop : Nat.Coprime (2 ^ (3 * k)) 3 := Nat.Coprime.pow_left _ (by norm_num)
  have hdvd3 : 2 ^ (3 * k) ∣ n := by
    have h : 2 ^ (3 * k) ∣ 3 * n := ⟨Y, h3⟩
    exact hcop.dvd_of_dvd_mul_left h
  have h1 : 2 ^ (3 * k + 1) ∣ m ! := by
    rw [← h2n, pow_succ']
    exact mul_dvd_mul_left 2 hdvd3
  have h2 : ¬ 2 ^ (3 * k + 1 + 1) ∣ m ! := by
    intro h
    have hx : 2 ^ (3 * k + 1 + 1) = 2 * (2 * 2 ^ (3 * k)) := by ring
    rw [hx, ← h2n] at h
    have h' : 2 * 2 ^ (3 * k) ∣ n := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
    have h'' : 2 * 2 ^ (3 * k) ∣ 2 ^ (3 * k) * Y := by
      rw [← h3]
      exact Dvd.dvd.mul_left h' 3
    have hy : 2 ^ (3 * k) * 2 ∣ 2 ^ (3 * k) * Y := by
      rw [mul_comm (2 ^ (3 * k)) 2]
      exact h''
    have h2Y : 2 ∣ Y := Nat.dvd_of_mul_dvd_mul_left (pow_pos two_pos _) hy
    obtain ⟨t, ht⟩ := hY
    omega
  exact (emultiplicity_eq_coe).2 ⟨h1, h2⟩

theorem three_mul_add_one_lt_of_factorial {m n k Y : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (h2n : 2 * n = m !)
    (h3 : 3 * n = 2 ^ (3 * k) * Y) (hY : Odd Y) : 3 * k + 1 < m := by
  have hlt := Nat.emultiplicity_two_factorial_lt (n := m) (by omega)
  rw [factorial_two_emultiplicity hk h2n h3 hY] at hlt
  exact_mod_cast hlt

theorem two_pow_le_factorial_of_three_le {k : ℕ} (hk : 3 ≤ k) : 2 ^ (8 * k + 1) ≤ (3 * k + 2) ! := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ k hk ih =>
    have e1 : 3 * (k + 1) + 2 = (3 * k + 2) + 1 + 1 + 1 := by ring
    have e2 : (3 * k + 2 + 1 + 1 + 1) ! = (3 * k + 5) * (3 * k + 4) * (3 * k + 3) * (3 * k + 2) ! := by
      rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
      ring
    have e3 : 2 ^ (8 * (k + 1) + 1) = 2 ^ 8 * 2 ^ (8 * k + 1) := by
      rw [← pow_add]
      ring_nf
    rw [e1, e2, e3]
    have hpos : 256 ≤ (3 * k + 5) * (3 * k + 4) * (3 * k + 3) := by
      have a1 : 14 ≤ 3 * k + 5 := by omega
      have a2 : 13 ≤ 3 * k + 4 := by omega
      have a3 : 12 ≤ 3 * k + 3 := by omega
      calc 256 ≤ 14 * 13 * 12 := by norm_num
        _ ≤ (3 * k + 5) * (3 * k + 4) * (3 * k + 3) := Nat.mul_le_mul (Nat.mul_le_mul a1 a2) a3
    calc 2 ^ 8 * 2 ^ (8 * k + 1) ≤ 2 ^ 8 * (3 * k + 2) ! := Nat.mul_le_mul_left _ ih
      _ = 256 * (3 * k + 2) ! := by norm_num
      _ ≤ (3 * k + 5) * (3 * k + 4) * (3 * k + 3) * (3 * k + 2) ! :=
          Nat.mul_le_mul_right _ hpos

theorem arith_core {k m n Y : ℕ} (hk : 2 ≤ k) (hm : 5 ≤ m) (h2n : 2 * n = m !)
    (h3 : 3 * n = (2 ^ k) ^ 3 * Y) (hY : Odd Y) (hYle : Y ≤ 2 * (2 ^ k) ^ 5) :
    k = 2 ∧ m = 8 ∧ Y = 945 := by
  have hpow3 : (2 ^ k) ^ 3 = 2 ^ (3 * k) := by rw [← pow_mul, mul_comm]
  rw [hpow3] at h3
  have hlt := three_mul_add_one_lt_of_factorial (by omega) (by omega) h2n h3 hY
  have hsize : m ! < 2 ^ (8 * k + 1) := by
    have h1 : 3 * n ≤ 2 ^ (3 * k) * (2 * (2 ^ k) ^ 5) := by
      rw [← hpow3]
      rw [← hpow3] at h3
      exact le_trans (le_of_eq h3) (Nat.mul_le_mul_left _ hYle)
    have e : 2 ^ (3 * k) * (2 * (2 ^ k) ^ 5) = 2 ^ (8 * k + 1) := by ring
    rw [e] at h1
    have hpos : 0 < 2 ^ (8 * k + 1) := by positivity
    omega
  have hk2 : k = 2 := by
    by_contra hne
    have hk3 : 3 ≤ k := by omega
    have hbig := two_pow_le_factorial_of_three_le hk3
    have hmono := Nat.factorial_le (show 3 * k + 2 ≤ m by omega)
    omega
  subst hk2
  have hm8 : m = 8 := by
    by_contra hne
    have hm9 : 9 ≤ m := by omega
    have := Nat.factorial_le hm9
    norm_num [Nat.factorial] at hsize this
    omega
  subst hm8
  have hn : n = 20160 := by
    norm_num [Nat.factorial] at h2n
    omega
  subst hn
  norm_num at h3
  omega

theorem l3Order_factorial {s n m : ℕ} (hm : 5 ≤ m) (h2n : 2 * n = m !) (hL : L3Order 2 s n) :
    s = 3 ∧ m = 8 ∧ n = 20160 := by
  obtain ⟨⟨k, hk1, hkr⟩, hPM⟩ := hL
  have hs_odd : s % 2 = 1 := by
    have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    rw [← hkr] at h2dvd
    omega
  have hpow : 2 ^ k = s + 1 := hkr.symm
  rcases hPM with ⟨hmod, hs3, h3⟩ | ⟨hmod, hs4, h3⟩
  ·
    have hk2 : 2 ≤ k := by
      by_contra hne
      have hk1' : k ≤ 1 := by omega
      interval_cases k <;> norm_num at hpow <;> omega
    have hYodd : Odd (s * (s + 2) * (s * (s ^ 2 + 3 * s + 3))) := by
      rw [Nat.odd_iff]
      simp [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, hs_odd]
    have hYle : s * (s + 2) * (s * (s ^ 2 + 3 * s + 3)) ≤ 2 * (2 ^ k) ^ 5 := by
      rw [hpow]
      have a1 : s * (s + 2) ≤ (s + 1) ^ 2 := by nlinarith
      have a2 : s * (s ^ 2 + 3 * s + 3) ≤ (s + 1) ^ 3 := by nlinarith
      calc s * (s + 2) * (s * (s ^ 2 + 3 * s + 3)) ≤ (s + 1) ^ 2 * (s + 1) ^ 3 := Nat.mul_le_mul a1 a2
        _ = (s + 1) ^ 5 := by ring
        _ ≤ 2 * (s + 1) ^ 5 := Nat.le_mul_of_pos_left _ (by norm_num)
    have h3' : 3 * n = (2 ^ k) ^ 3 * (s * (s + 2) * (s * (s ^ 2 + 3 * s + 3))) := by
      rw [hpow]
      exact h3
    obtain ⟨hk, hm8, -⟩ := arith_core hk2 hm h2n h3' hYodd hYle
    have hs3' : s = 3 := by
      rw [hk] at hpow
      norm_num at hpow
      omega
    subst hm8
    refine ⟨hs3', rfl, ?_⟩
    norm_num [Nat.factorial] at h2n
    omega
  ·
    exfalso
    have hk3 : 3 ≤ k := by
      by_contra hne
      have hk2' : k ≤ 2 := by omega
      interval_cases k <;> norm_num at hpow <;> omega
    have hYodd : Odd (s * (s + 2) * ((s + 2) * (s ^ 2 + s + 1))) := by
      rw [Nat.odd_iff]
      simp [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, hs_odd]
    have hYle : s * (s + 2) * ((s + 2) * (s ^ 2 + s + 1)) ≤ 2 * (2 ^ k) ^ 5 := by
      rw [hpow]
      have a1 : s * (s + 2) ≤ (s + 1) ^ 2 := by nlinarith
      have a2 : (s + 2) * (s ^ 2 + s + 1) ≤ (s + 1) ^ 3 + 1 := by nlinarith
      calc s * (s + 2) * ((s + 2) * (s ^ 2 + s + 1)) ≤ (s + 1) ^ 2 * ((s + 1) ^ 3 + 1) :=
            Nat.mul_le_mul a1 a2
        _ ≤ 2 * (s + 1) ^ 5 := by
          have h52 : (s + 1) ^ 2 ≤ (s + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
          have e : (s + 1) ^ 2 * ((s + 1) ^ 3 + 1) = (s + 1) ^ 5 + (s + 1) ^ 2 := by ring
          rw [e]
          linarith
    have h3' : 3 * n = (2 ^ k) ^ 3 * (s * (s + 2) * ((s + 2) * (s ^ 2 + s + 1))) := by
      rw [hpow]
      exact h3
    obtain ⟨hk, -, -⟩ := arith_core (by omega) hm h2n h3' hYodd hYle
    omega

end CFSG.LocalAnalysis.GLTheoremA.H1419
