module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace CFSG.GH74.GLS.IVK

section Cyclic

variable {G : Type*} [Group G] (g : G)

theorem orderOf_pow_odd_part {a m : ℕ} (hm : 0 < m) (h : orderOf g = 2 ^ a * m) :
    orderOf (g ^ m) = 2 ^ a := by
  rw [orderOf_pow' g hm.ne', h]
  have : Nat.gcd (2 ^ a * m) m = m := Nat.gcd_eq_right (Dvd.intro_left _ rfl)
  rw [this, Nat.mul_div_cancel _ hm]

theorem orderOf_pow_two_part {a m : ℕ} (h : orderOf g = 2 ^ a * m) :
    orderOf (g ^ (2 ^ a)) = m := by
  have h2 : 0 < 2 ^ a := by positivity
  rw [orderOf_pow' g h2.ne', h]
  have : Nat.gcd (2 ^ a * m) (2 ^ a) = 2 ^ a := Nat.gcd_eq_right (Dvd.intro _ rfl)
  rw [this, Nat.mul_div_cancel_left _ h2]

theorem orderOf_pow_half {a m : ℕ} (ha : 1 ≤ a) (h : orderOf g = 2 ^ a * m) :
    orderOf (g ^ (2 ^ (a - 1))) = 2 * m := by
  have h2 : 0 < 2 ^ (a - 1) := by positivity
  have h3 : 2 ^ a * m = 2 ^ (a - 1) * (2 * m) := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  rw [orderOf_pow' g h2.ne', h, h3]
  have : Nat.gcd (2 ^ (a - 1) * (2 * m)) (2 ^ (a - 1)) = 2 ^ (a - 1) :=
    Nat.gcd_eq_right (Dvd.intro _ rfl)
  rw [this, Nat.mul_div_cancel_left _ h2]

theorem exists_zpow_of_pow_eq_one {d n : ℕ} (hn : orderOf g = n) (hd : d ∣ n) (hdpos : 0 < d) (k : ℤ)
    (hk : (g ^ k) ^ d = 1) : ∃ k' : ℤ, g ^ k = (g ^ (n / d)) ^ k' := by
  obtain ⟨c, hc⟩ := hd
  have hc' : n / d = c := by rw [hc]; exact Nat.mul_div_cancel_left c hdpos
  have h1 : g ^ (k * (d : ℤ)) = 1 := by
    rw [zpow_mul]
    simpa using hk
  have h2 : (orderOf g : ℤ) ∣ k * d := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hn, hc, Nat.cast_mul, mul_comm k] at h2
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have h3 : (c : ℤ) ∣ k := (Int.mul_dvd_mul_iff_left hd0).mp h2
  obtain ⟨k', hk'⟩ := h3
  refine ⟨k', ?_⟩
  rw [hc', hk', zpow_mul, zpow_natCast]

end Cyclic

end CFSG.GH74.GLS.IVK
