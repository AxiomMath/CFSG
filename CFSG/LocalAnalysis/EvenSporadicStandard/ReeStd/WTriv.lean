module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.ReeStd

theorem eq_one_of_odd_pow_of_fixes_involutions {A : Type*} [Group A] [Finite A]
    (hA : ∀ a b : A, a * b = b * a) (hA2 : IsPGroup 2 A) (ψ : MulAut A) {m : ℕ} (hm : Odd m)
    (hψ : ψ ^ m = 1) (hfix : ∀ a : A, a * a = 1 → ψ a = a) : ψ = 1 := by
  have P : ∀ k : ℕ, ∀ a : A, a ^ 2 ^ k = 1 → ψ a = a := by
    intro k
    induction k with
    | zero =>
        intro a ha
        simp only [pow_zero, pow_one] at ha
        rw [ha, map_one]
    | succ k ih =>
        intro a ha
        have hpow : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
        have h2 : a ^ 2 ^ k * a ^ 2 ^ k = 1 := by rw [← pow_add, hpow, ha]
        have hfix2 : ψ (a ^ 2 ^ k) = a ^ 2 ^ k := hfix _ h2
        have hψa2 : (ψ a) ^ 2 ^ k = a ^ 2 ^ k := by rw [← map_pow, hfix2]
        set b : A := ψ a * a⁻¹ with hb
        have hbpow : b ^ 2 ^ k = 1 := by
          rw [hb]
          rw [(show Commute (ψ a) a⁻¹ from hA (ψ a) a⁻¹).mul_pow]
          rw [hψa2, inv_pow, mul_inv_cancel]
        have hψb : ψ b = b := ih b hbpow
        have hpsi_a : ψ a = b * a := by
          rw [hb, mul_assoc, inv_mul_cancel, mul_one]
        have hmain : ∀ n : ℕ, (ψ ^ n) a = a * b ^ n := by
          intro n
          induction n with
          | zero => simp
          | succ n ihn =>
              rw [pow_succ', MulAut.mul_apply, ihn, map_mul, map_pow, hψb, hpsi_a]
              rw [pow_succ, ← hA a b, mul_assoc, ← pow_succ', ← pow_succ]
        have hbm : b ^ m = 1 := by
          have h := hmain m
          rw [hψ, MulAut.one_apply] at h
          exact (mul_left_cancel (show a * 1 = a * b ^ m by rw [mul_one]; exact h)).symm
        have hcop : Nat.Coprime (2 ^ k) m := (Nat.coprime_two_left.mpr hm).pow_left k
        have horder : orderOf b = 1 :=
          Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_iff_pow_eq_one.mpr hbpow)
            (orderOf_dvd_iff_pow_eq_one.mpr hbm)
        have hb1 : b = 1 := orderOf_eq_one_iff.mp horder
        rw [hpsi_a, hb1, one_mul]
  ext a
  rcases hA2 a with ⟨k, hk⟩
  simpa using P k a hk

end CFSG.EvenSporadicStandard.ReeStd
