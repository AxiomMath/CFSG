module


public import Mathlib.Data.Nat.Prime.Basic

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.PrimePowerSquareRoot

theorem exists_exponent {p N m : ℕ} (hp : p.Prime) (h : N ^ 2 = p ^ m) :
    ∃ d, m = 2 * d ∧ N = p ^ d := by
  have hN : N ∣ p ^ m := by rw [← h]; exact Dvd.intro_left _ (sq N).symm
  obtain ⟨d, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hN
  refine ⟨d, ?_, rfl⟩
  rw [← pow_mul] at h
  have := Nat.pow_right_injective hp.two_le h
  omega

end CFSG.GroupTheory.CoprimeActionSupport.PrimePowerSquareRoot
