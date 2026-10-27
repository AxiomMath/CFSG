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

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2

abbrev Mat : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

abbrev Vec : Type := Fin 4 → ZMod 2

@[expose] def QuadRigid (ρ : Fin 2 → Mat) : Prop :=
  ∀ (δ : Vec) (γ : Fin 4 → Fin 4 → ZMod 2), (∀ i, γ i i = 0) → (∀ i l, γ i l = γ l i) →
    (∀ j i, δ i = ∑ m, ρ j i m * δ m +
      ∑ m, ∑ n, (if m < n then ρ j i m * ρ j i n * γ m n else 0)) →
    (∀ j i l, γ i l = ∑ m, ∑ n, ρ j i m * ρ j l n * γ m n) →
    δ = 0 ∧ γ = 0

@[expose] def SplitRigid (ρ : Fin 2 → Mat) : Prop :=
  ∀ (ε : Fin 2 → Vec) (β : Fin 4 → Fin 4 → Vec), (∀ i, β i i = 0) → (∀ i l, β i l = β l i) →
    (∀ j i l, Matrix.vecMul (β i l) (ρ j) =
      ∑ m, ∑ n, (ρ j i m * ρ j l n) • β m n +
        ε j l • Matrix.vecMul (Pi.single i 1) (ρ j) + ε j i • Matrix.vecMul (Pi.single l 1) (ρ j)) →
    ∃ f : Vec, (∀ j i, ε j i = f i + ∑ l, ρ j i l * f l) ∧
      ∀ i l, β i l = f i • Pi.single l 1 + f l • Pi.single i 1

@[expose] def CommRigid (ρ : Fin 2 → Mat) : Prop :=
  ∀ S : Mat, (∀ j, ρ j * S = S * ρ j) → S = 0 ∨ S = 1

@[expose] def red (X : Matrix (Fin 4) (Fin 4) (ZMod 4)) : Mat :=
  X.map (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2))

@[expose] def Z4Rigid (x y : Mat) : Prop :=
  ∀ X Y : Matrix (Fin 4) (Fin 4) (ZMod 4), red X = x → red Y = y → X * X = 1 → Y * Y = 1 →
    X * Y * (X * Y) ≠ 1

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2
