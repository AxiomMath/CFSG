module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

theorem sq_mod_eq_one {q r : ℕ} (hq : IsPrimePow q) (h2 : 2 ∣ q) (hr : r * r % (4 * q) = 1) :
    r % (4 * q) = 1 ∨ r % (4 * q) = 2 * q + 1 ∨ r % (4 * q) = 2 * q - 1 ∨
      r % (4 * q) = 4 * q - 1 := by
  have hq2 : 2 ≤ q := Nat.le_of_dvd (hq.pos) h2
  have hq4 : 0 < 4 * q := by omega
  have hodd : r % 2 = 1 := by
    by_contra hcon
    have hev : r % 2 = 0 := by omega
    have h1 : 2 ∣ r * r := Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero hev) r
    have h4 : 2 ∣ 4 * q := ⟨2 * q, by ring⟩
    have h5 : 2 ∣ r * r % (4 * q) := (Nat.dvd_mod_iff h4).mpr h1
    rw [hr] at h5
    omega
  obtain ⟨t, rfl⟩ : ∃ t, r = 2 * t + 1 := ⟨r / 2, by omega⟩
  have hsq : (2 * t + 1) * (2 * t + 1) = 4 * (t * (t + 1)) + 1 := by ring
  have hdvd : 4 * q ∣ 4 * (t * (t + 1)) := by
    have h1 : (2 * t + 1) * (2 * t + 1) % (4 * q) = 1 % (4 * q) := by
      rw [hr, Nat.mod_eq_of_lt (by omega)]
    have h2 := (Nat.modEq_iff_dvd' (by omega)).mp h1.symm
    rw [hsq] at h2
    simpa using h2
  have hdvd' : q ∣ t * (t + 1) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hcop : Nat.Coprime t (t + 1) := by simp
  rcases (Nat.Coprime.isPrimePow_dvd_mul hcop hq).mp hdvd' with ⟨s, hs⟩ | ⟨s, hs⟩
  ·
    rcases Nat.even_or_odd' s with ⟨u, rfl | rfl⟩
    · left
      have : 2 * t + 1 = 1 + 4 * q * u := by rw [hs]; ring
      rw [this, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    · right; left
      have : 2 * t + 1 = (2 * q + 1) + 4 * q * u := by rw [hs]; ring
      rw [this, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
  ·
    rcases Nat.even_or_odd' s with ⟨u, rfl | rfl⟩
    · right; right; right
      have hu : 1 ≤ u := by
        rcases Nat.eq_zero_or_pos u with h0 | h0
        · subst h0
          omega
        · exact h0
      have : 2 * t + 1 = (4 * q - 1) + 4 * q * (u - 1) := by
        obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
        have h3 : t + 1 = q * (2 * (v + 1)) := hs
        have h4 : 2 * t + 1 = 4 * q * (v + 1) - 1 := by
          have : 2 * (t + 1) = 4 * q * (v + 1) := by rw [h3]; ring
          omega
        rw [h4]
        simp only [Nat.add_sub_cancel]
        have h5 : 4 * q * (v + 1) = 4 * q * v + 4 * q := by ring
        omega
      rw [this, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    · right; right; left
      have : 2 * t + 1 = (2 * q - 1) + 4 * q * u := by
        have h3 : t + 1 = q * (2 * u + 1) := hs
        have h4 : 2 * (t + 1) = 4 * q * u + 2 * q := by rw [h3]; ring
        omega
      rw [this, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)

theorem dvd_of_dvd_mul_pred {n j : ℕ} (hn : 4 ≤ n) (h : 2 ^ (n - 1) ∣ (2 ^ (n - 2) - 2) * j) :
    2 ^ (n - 2) ∣ j := by
  have h1 : 2 ^ (n - 2) = 2 * 2 ^ (n - 3) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have hev : 2 ∣ 2 ^ (n - 3) := dvd_pow_self 2 (by omega)
  have hge : 2 ≤ 2 ^ (n - 3) := Nat.le_of_dvd (by positivity) hev
  have h3 : 2 ^ (n - 2) - 2 = 2 * (2 ^ (n - 3) - 1) := by omega
  rw [h2, h3, mul_assoc] at h
  have h4 : 2 ^ (n - 2) ∣ (2 ^ (n - 3) - 1) * j := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hodd : Nat.Coprime (2 ^ (n - 3) - 1) 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  exact (Nat.Coprime.pow_right (n - 2) hodd).symm.dvd_of_dvd_mul_left h4

end CFSG.GH74.Uniqueness.SU.SU1
