module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Signs

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix

variable {K : Type} [Field K] {n : ℕ}

theorem IsMonomialFor.pow {M : Matrix (Fin n) (Fin n) K} {τ : Equiv.Perm (Fin n)}
    (h : IsMonomialFor M τ) (m : ℕ) : IsMonomialFor (M ^ m) (τ ^ m) := by
  induction m with
  | zero => simpa using isMonomialFor_one
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

end CFSG.ClassicalInvolution.Models

end
