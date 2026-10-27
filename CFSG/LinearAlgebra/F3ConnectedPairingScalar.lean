module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.LinearAlgebra

open Module

theorem zmod_three_eq_one_or_neg_one : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by decide

end CFSG.LinearAlgebra
