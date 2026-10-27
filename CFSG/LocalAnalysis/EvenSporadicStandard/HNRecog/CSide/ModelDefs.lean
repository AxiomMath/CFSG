module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Normalize
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf CFSG.EvenSporadicStandard.HNRecog.Swap

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

def cSideFixedNondeg (q : QuadraticForm (ZMod 2) V) (f : V ≃ₗ[ZMod 2] V) : Prop :=
  ∀ v : V, f v = v → v ≠ 0 → ∃ w : V, f w = w ∧ QuadraticMap.polar q v w ≠ 0

def cSideFixedPlane (q : QuadraticForm (ZMod 2) V) (f : V ≃ₗ[ZMod 2] V) : Prop :=
  ∃ v w : V, f v = v ∧ f w = w ∧ v ≠ 0 ∧ w ≠ 0 ∧ v ≠ w ∧ q v = 0 ∧ q w = 0 ∧
    QuadraticMap.polar q v w = 0

def cSideFreeSwap (q : QuadraticForm (ZMod 2) V) (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V))
    (b : V ≃ₗ[ZMod 2] V) : Prop :=
  b * b = 1 ∧ (∀ v, q (b v) = q v) ∧ SwapsFactors σ b ∧
    4 ≤ finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) + 1))

def CSideFixedZero (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ g : A5 × A5, (orderOf g = 3 ∨ orderOf g = 5) → (g.1 = 1 ∨ g.2 = 1) →
    ∀ v : V, σ g v = v → v = 0

def CSideThreeBoth (q : QuadraticForm (ZMod 2) V) (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ g : A5 × A5, orderOf g = 3 → g.1 ≠ 1 → g.2 ≠ 1 →
    Nat.card {v : V // σ g v = v} = 16 ∧ cSideFixedNondeg q (σ g) ∧ cSideFixedPlane q (σ g)

def CSideInvol (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ g : A5 × A5, g ≠ 1 → g ^ 2 = 1 → Nat.card {v : V // σ g v = v} = 16

def CSideOrbits (q : QuadraticForm (ZMod 2) V) (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∃ O : Fin 2 → Set V, (∀ v : V, (v ≠ 0 ∧ q v = 0) ↔ ∃ i, v ∈ O i) ∧
    (∀ i j, i ≠ j → Disjoint (O i) (O j)) ∧
    (∀ i, ∀ g : A5 × A5, ∀ v ∈ O i, σ g v ∈ O i) ∧
    (∀ i, ∀ v ∈ O i, ∀ w ∈ O i, ∃ g : A5 × A5, σ g v = w) ∧
    Nat.card (O 0) = 75 ∧ Nat.card (O 1) = 60

def CSideFiveBoth (q : QuadraticForm (ZMod 2) V) (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ b : V ≃ₗ[ZMod 2] V, cSideFreeSwap q σ b →
    ∀ g : A5 × A5, orderOf g = 5 → g.1 ≠ 1 → g.2 ≠ 1 →
      ((∃ l : A5 × A5, σ l * b * σ g = σ g * (σ l * b)) → ∀ v : V, σ g v = v → v = 0) ∧
      ((¬ ∃ l : A5 × A5, σ l * b * σ g = σ g * (σ l * b)) →
        Nat.card {v : V // σ g v = v} = 16 ∧ cSideFixedNondeg q (σ g) ∧
          ¬ cSideFixedPlane q (σ g))

def CSideOmega (q : QuadraticForm (ZMod 2) V) (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∃ ω : V ≃ₗ[ZMod 2] V, (∀ g : A5 × A5, ω * σ g = σ g * ω) ∧
    (∀ v : V, ω (ω v) + ω v + v = 0) ∧
    ∀ b : V ≃ₗ[ZMod 2] V, cSideFreeSwap q σ b → ∀ v : V, b (ω v) = ω (ω (b v))

structure CSideModel (q : QuadraticForm (ZMod 2) V) (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) :
    Prop where
  fixed_zero : CSideFixedZero σ
  three_both : CSideThreeBoth q σ
  invol : CSideInvol σ
  orbits : CSideOrbits q σ
  five_both : CSideFiveBoth q σ
  omega : CSideOmega q σ

end CFSG.EvenSporadicStandard.HNRecog.CSide
