module

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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GF2Type.CenterFour

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem linearIndependent_castSucc_of_pairwise (b : LinearMap.BilinForm (ZMod 2) V)
    (hb : b.IsAlt) {s : ℕ} (f : Fin (s + 1) → V) (hf : ∀ i j, i ≠ j → b (f i) (f j) = 1) :
    LinearIndependent (ZMod 2) (fun i : Fin s => f i.castSucc) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have pair : ∀ v : V, ∑ i : Fin s, g i * b (f i.castSucc) v = 0 := by
    intro v
    have h := congrArg (fun w => b w v) hg
    simpa [map_sum, smul_eq_mul] using h
  have hS : ∑ i : Fin s, g i = 0 := by
    have h1 : ∀ i : Fin s, b (f i.castSucc) (f (Fin.last s)) = 1 := fun i =>
      hf _ _ (Fin.castSucc_lt_last i).ne
    simpa [h1] using pair (f (Fin.last s))
  intro j
  have hB : ∀ i : Fin s, b (f i.castSucc) (f j.castSucc) = 1 + if i = j then 1 else 0 := by
    intro i
    split_ifs with hij
    · subst hij
      rw [hb (f i.castSucc)]
      decide
    · rw [add_zero]
      exact hf i.castSucc j.castSucc (fun h => hij (Fin.castSucc_injective _ h))
  have hj := pair (f j.castSucc)
  simp [hB, mul_add, mul_ite, Finset.sum_add_distrib] at hj
  linear_combination hj - hS

theorem card_le_finrank_add_one [FiniteDimensional (ZMod 2) V] (b : LinearMap.BilinForm (ZMod 2) V)
    (hb : b.IsAlt) {s : ℕ} (f : Fin s → V) (hf : ∀ i j, i ≠ j → b (f i) (f j) = 1) :
    s ≤ Module.finrank (ZMod 2) V + 1 := by
  cases s with
  | zero => exact Nat.zero_le _
  | succ n =>
    have hli := linearIndependent_castSucc_of_pairwise b hb f hf
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_fin] at hle
    omega

end CFSG.GF2Type.CenterFour
