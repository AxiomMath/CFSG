module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

theorem mem_range_scalar_of_commute_span {K : Type*} [Field K] {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n K) (S : Set (Matrix n n K))
    (hS : Submodule.span K S = ⊤) (hA : ∀ s ∈ S, A * s = s * A) :
    A ∈ Set.range (Matrix.scalar n) := by
  have hall : ∀ x : Matrix n n K, A * x = x * A := by
    intro x
    have hx : x ∈ Submodule.span K S := by rw [hS]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact hA y hy
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, add_mul, hy, hz]
    | smul a y _ hy => rw [Matrix.mul_smul, hy, Matrix.smul_mul]
  exact Matrix.mem_range_scalar_iff_commute_single'.2 fun i j => (hall _).symm

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving
