module

public import Mathlib.RingTheory.Polynomial.Chebyshev

public section

namespace CFSG.LinearAlgebra

open Polynomial

theorem pow_succ_eq_chebyshevS {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {τ : R}
    {x : A} (hx : x ^ 2 = τ • x - 1) (n : ℕ) :
    x ^ (n + 1) = (Chebyshev.S R n).eval τ • x - (Chebyshev.S R ((n : ℤ) - 1)).eval τ • 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ih, mul_sub, mul_smul_comm, mul_smul_comm, ← sq, mul_one, hx,
      Nat.cast_succ, add_sub_cancel_right, Chebyshev.S_add_one, eval_sub, eval_mul, eval_X]
    module

end CFSG.LinearAlgebra
