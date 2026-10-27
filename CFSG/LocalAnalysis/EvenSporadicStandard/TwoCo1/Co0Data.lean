module

public import CFSG.Monster.CodeAut.Perm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster.Code

@[expose] def oct₁ : C := ⟨bvec 24 255, by decide⟩

@[expose] def dod₂ : C := ⟨bvec 24 212822, by decide⟩

theorem hammingNorm_oct₁ : hammingNorm (oct₁ : Fin 24 → ZMod 2) = 8 := by
  show hammingNorm (bvec 24 255) = 8
  rw [hammingNorm_bvec]
  decide

theorem hammingNorm_dod₂ : hammingNorm (dod₂ : Fin 24 → ZMod 2) = 12 := by
  show hammingNorm (bvec 24 212822) = 12
  rw [hammingNorm_bvec]
  decide

@[expose] def tEl : Equiv.Perm (Fin 24) where
  toFun := ![14, 8, 4, 7, 17, 18, 10, 15, 2, 1, 11, 13, 9, 12, 23, 20, 16, 6, 22, 3, 0, 21, 19, 5]
  invFun := ![20, 9, 8, 19, 2, 23, 17, 3, 1, 12, 6, 10, 13, 11, 0, 7, 16, 4, 5, 22, 15, 21, 18, 14]
  left_inv := by decide
  right_inv := by decide

private theorem tEl_basis : ∀ i, B i ∘ ⇑tEl ∈ C := by decide

private theorem tEl_basis' : ∀ i, B i ∘ ⇑tEl⁻¹ ∈ C := by decide

theorem tEl_mem : tEl ∈ AutPerm := mem_AutPerm_of_basis tEl_basis tEl_basis'

theorem tEl_pow_eleven : tEl ^ 11 = 1 := Equiv.ext fun i => by revert i; decide

theorem tEl_ne_one : tEl ≠ 1 := fun h => by
  have := congrArg (fun f : Equiv.Perm (Fin 24) => f 0) h
  revert this
  decide

theorem permWord_tEl_dod₂ : permWord tEl (dod₂ : Fin 24 → ZMod 2) = dod₂ := by
  funext i
  revert i
  decide

@[expose] def sigEl : Equiv.Perm (Fin 24) where
  toFun := ![16, 22, 3, 2, 5, 4, 23, 17, 15, 14, 19, 20, 18, 21, 9, 8, 0, 7, 12, 10, 11, 13, 1, 6]
  invFun := ![16, 22, 3, 2, 5, 4, 23, 17, 15, 14, 19, 20, 18, 21, 9, 8, 0, 7, 12, 10, 11, 13, 1, 6]
  left_inv := by decide
  right_inv := by decide

private theorem sigEl_basis : ∀ i, B i ∘ ⇑sigEl ∈ C := by decide

private theorem sigEl_basis' : ∀ i, B i ∘ ⇑sigEl⁻¹ ∈ C := by decide

theorem sigEl_mem : sigEl ∈ AutPerm := mem_AutPerm_of_basis sigEl_basis sigEl_basis'

theorem permWord_sigEl_dod₂ :
    permWord sigEl (dod₂ : Fin 24 → ZMod 2) = (dod₂ : Fin 24 → ZMod 2) + Ω := by
  funext i
  revert i
  decide

end CFSG.EvenSporadicStandard.TwoCo1
