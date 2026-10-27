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

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629

open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

structure RShape (p d : ℕ) (R : Subgroup K) (t : K) : Prop where
  pd : (p = 3 ∧ d = 2) ∨ (p = 5 ∧ d = 4)
  card : Nat.card R = 2 ^ (d + 1)
  t_mem : t ∈ R
  t_sq : t ^ 2 = 1
  t_ne : t ≠ 1
  t_comm : ∀ r ∈ R, r * t = t * r
  center_le : ∀ y ∈ R, (∀ r ∈ R, y * r = r * y) → y ∈ zpowers t
  sq_mem : ∀ r ∈ R, r ^ 2 ∈ zpowers t
  comm_mem : ∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ zpowers t
  sqrt : ∃ i ∈ R, i ^ 2 = t

structure Setup (p d : ℕ) (S : Subgroup K) (z t : K) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  two : IsPGroup 2 S
  zp : z ^ p = 1
  zne : z ≠ 1
  zS : zpowers z ≤ normalizer (S : Set K)
  shape : RShape p d ⁅zpowers z, S⁆ t

structure FData (f : ℕ) (F : Subgroup K) : Prop where
  prime : f.Prime
  odd : f ≠ 2
  comm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a
  exp : ∀ a ∈ F, a ^ f = 1
  ne : F ≠ ⊥

abbrev RR (S : Subgroup K) (z : K) : Subgroup K := ⁅zpowers z, S⁆

abbrev CC (S : Subgroup K) (z : K) : Subgroup K :=
  S ⊓ centralizer ((RR S z : Subgroup K) : Set K)

@[expose] def LAEven (f : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod f) V] [Module.Finite (ZMod f) V]
    (x y : Module.End (ZMod f) V), x * x = -1 → y * y = -1 → y * x = -(x * y) →
      Even (Module.finrank (ZMod f) V)

@[expose] def LAScalar (f : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod f) V] [Module.Finite (ZMod f) V],
    Module.finrank (ZMod f) V = 2 →
      ∀ (x y c : Module.End (ZMod f) V), x * x = -1 → y * y = -1 → y * x = -(x * y) →
        c * x = x * c → c * y = y * c → ∃ μ : ZMod f, c = μ • (1 : Module.End (ZMod f) V)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
