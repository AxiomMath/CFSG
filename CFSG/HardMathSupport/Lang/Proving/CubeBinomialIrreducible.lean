module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import CFSG.HardMathSupport.Lang.Proving.CubeClassCyclic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Lang.Proving

open Polynomial

theorem irreducible_X_pow_three_sub_C_of_not_cube {K : Type*} [Field K] (lam : K)
    (hlam : ∀ y : K, y ^ 3 ≠ lam) : Irreducible (X ^ 3 - C lam) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, natDegree_X_pow_sub_C]
    omega
  · intro y hy
    apply hlam y
    simpa [IsRoot, sub_eq_zero] using hy

end CFSG.HardMathSupport.Lang.Proving

end
