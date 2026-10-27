module

public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
namespace KSE8Five
namespace One

theorem inner_swap_identity {K : Type} [Field K] {ω : K} (hω0 : ω ≠ 0) (s : Fin 5) (c t : K)
    (hc : c ≠ 0) (ht : t ≠ 0) :
    c • (Matrix.of (fun l k : Fin 5 => if l = k + s then (1 : K) else 0) *
        Matrix.diagonal (fun i : Fin 5 => if i = 0 then t else 1)) =
      Matrix.diagonal (fun i : Fin 5 =>
          (if i = 0 then t else 1) * (c * ω ^ ((s : ℕ) * (i : ℕ)))) *
        (Matrix.of (fun l k : Fin 5 => if l = k + s then (1 : K) else 0) *
          Matrix.diagonal (fun k : Fin 5 =>
            (if k = 0 then t else 1) *
              ((if k + s = 0 then t else 1) * ω ^ ((s : ℕ) * ((k + s : Fin 5) : ℕ)))⁻¹)) := by
  have hf : ∀ j : Fin 5, (if j = 0 then t else 1) ≠ 0 := fun j => by
    split_ifs <;> simp [ht]
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.of_apply]
  by_cases h : i = k + s
  · rw [if_pos h]
    subst h
    have h1 := hf (k + s)
    have h2 := hf k
    have hW : ω ^ ((s : ℕ) * ((k + s : Fin 5) : ℕ)) ≠ 0 := pow_ne_zero _ hω0
    field_simp
  · rw [if_neg h]
    simp

end One
end KSE8Five
end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
