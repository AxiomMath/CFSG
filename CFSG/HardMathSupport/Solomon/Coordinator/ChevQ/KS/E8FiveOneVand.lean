module

public import Mathlib.LinearAlgebra.Vandermonde

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

theorem diagonal_mul_vandermonde_five {K : Type} [Field K] {ω : K} (hω : ω ^ 5 = 1) (s : Fin 5) :
    Matrix.diagonal (fun i : Fin 5 => ω ^ ((s : ℕ) * (i : ℕ))) *
        Matrix.vandermonde (fun k : Fin 5 => ω ^ (k : ℕ)) =
      Matrix.vandermonde (fun k : Fin 5 => ω ^ (k : ℕ)) *
        Matrix.of (fun l k : Fin 5 => if l = k + s then (1 : K) else 0) := by
  have hexp : ∀ a b : ℕ, a % 5 = b % 5 → ω ^ a = ω ^ b := fun a b h => by
    rw [pow_eq_pow_mod a hω, pow_eq_pow_mod b hω, h]
  ext i k
  rw [Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [Matrix.vandermonde_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← pow_mul, ← pow_mul, ← pow_add]
  apply hexp
  rw [Fin.val_add, Nat.mul_mod_mod]
  congr 1
  ring

end One

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
