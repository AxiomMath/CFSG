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
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

universe u

theorem exists_blockEquiv {Ω : Type u} [Fintype Ω] [DecidableEq Ω] (σ : Ω → Ω)
    (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (e : Ω ≃ ι × Bool),
      Fintype.card Ω = 2 * Fintype.card ι ∧ ∀ x, e (σ x) = ((e x).1, !(e x).2) := by
  classical
  let ord : Ω ≃ Fin (Fintype.card Ω) := Fintype.equivFin Ω
  have hne : ∀ x, ord x ≠ ord (σ x) := fun x h => hσ1 x (ord.injective h).symm
  have hlt : ∀ x, ¬ ord x < ord (σ x) → ord (σ x) < ord x := fun x h =>
    lt_of_le_of_ne (not_lt.1 h) (hne x).symm
  let ι := {x : Ω // ord x < ord (σ x)}
  let f : Ω → ι × Bool := fun x =>
    if h : ord x < ord (σ x) then (⟨x, h⟩, true)
    else (⟨σ x, by rw [hσ2]; exact hlt x h⟩, false)
  let g : ι × Bool → Ω := fun p => if p.2 then p.1.1 else σ p.1.1
  have hgf : ∀ x, g (f x) = x := by
    intro x
    by_cases h : ord x < ord (σ x)
    · simp [f, g, h]
    · simp [f, g, h, hσ2]
  have hfg : ∀ p, f (g p) = p := by
    rintro ⟨⟨x, hx⟩, b⟩
    cases b
    · have h1 : ¬ ord (σ x) < ord x := not_lt.2 hx.le
      simp [f, g, h1, hσ2]
    · simp [f, g, hx]
  refine ⟨ι, inferInstance, inferInstance, ⟨f, g, hgf, hfg⟩, ?_, ?_⟩
  · have := Fintype.card_congr (⟨f, g, hgf, hfg⟩ : Ω ≃ ι × Bool)
    exact this.trans (by rw [Fintype.card_prod, Fintype.card_bool, mul_comm])
  · intro x
    by_cases h : ord x < ord (σ x)
    · have h2 : ¬ ord (σ x) < ord x := not_lt.2 h.le
      show f (σ x) = ((f x).1, !(f x).2)
      simp [f, h, h2, hσ2]
    · have h2 : ord (σ x) < ord x := hlt x h
      show f (σ x) = ((f x).1, !(f x).2)
      simp [f, h, h2, hσ2]

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
