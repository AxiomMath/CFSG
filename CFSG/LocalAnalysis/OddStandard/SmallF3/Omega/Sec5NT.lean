module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13dZig

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5nt_five_le {q s : ℕ} (hq : Odd q) (hs : s.Prime) (h : ¬ s ∣ q * (q ^ 2 - 1)) :
    5 ≤ s := by
  refine hs.five_le_of_ne_two_of_ne_three ?_ ?_
  · rintro rfl
    apply h
    have h1 : Even (q ^ 2 - 1) := Nat.Odd.sub_odd (hq.pow) odd_one
    exact Dvd.dvd.mul_left (even_iff_two_dvd.mp h1) q
  · rintro rfl
    apply h
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ hq.pos),
      Nat.cast_pow, Nat.cast_one]
    generalize (q : ZMod 3) = x
    revert x
    decide

theorem sec5nt_exists_prime_dvd {q₁ r : ℕ} (hq₁ : Odd q₁) (hq₃ : 3 ≤ q₁) (hr : r.Prime)
    (hr2 : r ≠ 2) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) :
    ∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧ (s : ℤ) ∣ (q₁ : ℤ) ^ r - δ ∧
      ¬ (s : ℤ) ∣ (q₁ : ℤ) * ((q₁ : ℤ) ^ 2 - 1) := by
  have key : ∃ s : ℕ, s.Prime ∧ (s : ℤ) ∣ (q₁ : ℤ) ^ r - δ ∧ ¬ s ∣ q₁ ^ 2 - 1 ∧ ¬ s ∣ q₁ := by
    rcases hδ with rfl | rfl
    · obtain ⟨s, hs, h1, h2, -, h4⟩ :=
        CFSG.GH74.GLS.IVK.Proofs2.exists_prime_dvd_pow_sub_one hr hr2 hq₁ hq₃
      refine ⟨s, hs, ?_, h2, h4⟩
      have h5 := Int.natCast_dvd_natCast.mpr h1
      rwa [Nat.cast_sub (Nat.one_le_pow _ _ hq₁.pos), Nat.cast_pow, Nat.cast_one] at h5
    · obtain ⟨s, hs, h1, h2, -, h4⟩ :=
        CFSG.GH74.GLS.IVK.Proofs2.exists_prime_dvd_pow_add_one hr hr2 hq₁ hq₃
      refine ⟨s, hs, ?_, h2, h4⟩
      have h5 := Int.natCast_dvd_natCast.mpr h1
      push_cast at h5
      simpa using h5
  obtain ⟨s, hs, h1, h2, h3⟩ := key
  have hnd : ¬ s ∣ q₁ * (q₁ ^ 2 - 1) := fun h => (hs.dvd_mul.mp h).elim h3 h2
  refine ⟨s, hs, sec5nt_five_le hq₁ hs hnd, h1, fun h => hnd ?_⟩
  have hc : ((q₁ * (q₁ ^ 2 - 1) : ℕ) : ℤ) = (q₁ : ℤ) * ((q₁ : ℤ) ^ 2 - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ hq₁.pos)]
    push_cast
    ring
  exact Int.natCast_dvd_natCast.mp (hc ▸ h)

end CFSG.OddStandard.SmallF3.Omega
