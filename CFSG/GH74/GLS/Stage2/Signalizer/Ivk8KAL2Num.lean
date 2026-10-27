module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.SL2MinimalFaithful

theorem kaL2_ppd_aux {q₁ n p : ℕ} (hq₁ : 3 ≤ q₁) (hq₁o : Odd q₁) (hn : 3 ≤ n) (hp : p.Prime)
    (hpn : p ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ∣ q₁ ^ n - 1 ∧ (∀ k : ℕ, 0 < k → k < n → ¬ r ∣ q₁ ^ k - 1) ∧
      r ≠ 2 ∧ r ≠ p ∧ ¬ r ∣ q₁ * (q₁ ^ 2 - 1) := by
  obtain ⟨r, hr, hr1, hprim⟩ := exists_primitive_prime_dvd_pow_sub_one hq₁ hn
  refine ⟨r, hr, hr1, hprim, ?_, ?_, ?_⟩
  · rintro rfl
    apply hprim 1 (by norm_num) (by omega)
    rw [pow_one]
    have h2 : q₁ % 2 = 1 := Nat.odd_iff.mp hq₁o
    omega
  · rintro rfl
    have : Fact r.Prime := ⟨hr⟩
    have ha0 : 0 < q₁ := by omega
    have h1 := (Zsigmondy.dvd_pow_sub_one_iff ha0 n).mp hr1
    have hne : (q₁ : ZMod r) ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega)] at h1
      exact zero_ne_one h1
    have h2 := ZMod.pow_card_sub_one_eq_one hne
    refine hprim (r - 1) ?_ ?_ ((Zsigmondy.dvd_pow_sub_one_iff ha0 (r - 1)).mpr h2)
    · have := hr.two_le
      omega
    · omega
  · intro h
    rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · have h3 : r ∣ q₁ ^ n := dvd_pow h (by omega)
      have h4 : r ∣ q₁ ^ n - (q₁ ^ n - 1) := Nat.dvd_sub h3 hr1
      have h5 : q₁ ^ n - (q₁ ^ n - 1) = 1 := by
        have : 1 ≤ q₁ ^ n := Nat.one_le_pow _ _ (by omega)
        omega
      rw [h5] at h4
      exact hr.one_lt.ne' (Nat.dvd_one.mp h4)
    · exact hprim 2 (by norm_num) (by omega) h

theorem kaL2_ppd {q₁ ℓ p d : ℕ} (hq₁ : 3 ≤ q₁) (hq₁o : Odd q₁) (hℓ : 3 ≤ ℓ) (hp : p.Prime)
    (hpℓ : p ∣ ℓ) (hd : d + 1 = q₁ ^ ℓ ∨ d = q₁ ^ ℓ + 1) :
    ∃ r : ℕ, r.Prime ∧ r ∣ d ∧ r ≠ 2 ∧ r ≠ p ∧ ¬ r ∣ q₁ * (q₁ ^ 2 - 1) := by
  have hpℓ' : p ≤ ℓ := Nat.le_of_dvd (by omega) hpℓ
  rcases hd with hd | hd
  · obtain ⟨r, hr, hr1, -, h2, hp', h3⟩ := kaL2_ppd_aux hq₁ hq₁o hℓ hp hpℓ'
    exact ⟨r, hr, by rwa [show d = q₁ ^ ℓ - 1 by omega], h2, hp', h3⟩
  · obtain ⟨r, hr, hr1, hprim, h2, hp', h3⟩ :=
      kaL2_ppd_aux hq₁ hq₁o (n := 2 * ℓ) (by omega) hp (by omega)
    have hX1 : 1 ≤ q₁ ^ ℓ := Nat.one_le_pow _ _ (by omega)
    have hsq : q₁ ^ (2 * ℓ) - 1 = (q₁ ^ ℓ + 1) * (q₁ ^ ℓ - 1) := by
      have : q₁ ^ (2 * ℓ) = q₁ ^ ℓ * q₁ ^ ℓ := by rw [two_mul, pow_add]
      rw [this]
      have := Nat.mul_self_sub_mul_self_eq (q₁ ^ ℓ) 1
      simpa using this
    rw [hsq] at hr1
    rcases (Nat.Prime.dvd_mul hr).mp hr1 with h | h
    · exact ⟨r, hr, by rwa [hd], h2, hp', h3⟩
    · exact absurd h (hprim ℓ (by omega) (by omega))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
