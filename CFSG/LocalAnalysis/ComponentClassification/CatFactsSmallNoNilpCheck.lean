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

namespace CFSG.ComponentClassification.CatFactsSmall

variable {n : ℕ}

@[expose, noinline] def pairWitness (C : List (Equiv.Perm (Fin n))) (m : ℕ) : Bool :=
  C.any fun x₁ => C.any fun x₂ => !(decide ((x₁ * x₂) ^ m = 1))

@[expose, noinline] def noNilpCheck (LA odd : List (Equiv.Perm (Fin n))) (m : ℕ) : Bool :=
  LA.all fun s => !(decide (s * s = 1)) ||
    pairWitness (odd.filter fun x => decide (x * s = s * x)) m

theorem noNilpCheck_sound {LA odd : List (Equiv.Perm (Fin n))} {m : ℕ}
    (h : noNilpCheck LA odd m = true) {s : Equiv.Perm (Fin n)} (hs : s ∈ LA) (hs2 : s * s = 1) :
    ∃ x₁ ∈ odd, ∃ x₂ ∈ odd, x₁ * s = s * x₁ ∧ x₂ * s = s * x₂ ∧ (x₁ * x₂) ^ m ≠ 1 := by
  have h1 := List.all_eq_true.1 h s hs
  simp only [pairWitness, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    List.any_eq_true, List.mem_filter, decide_eq_true_eq] at h1
  rcases h1 with h1 | ⟨x₁, ⟨hx₁, hc₁⟩, x₂, ⟨hx₂, hc₂⟩, h12⟩
  · exact absurd hs2 h1
  · exact ⟨x₁, hx₁, x₂, hx₂, hc₁, hc₂, h12⟩

end CFSG.ComponentClassification.CatFactsSmall
