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

namespace CFSG.ComponentClassification.WittDesign

open Equiv

@[expose] def latinSq (r : Fin 3 → Perm (Fin 4)) (x y : Fin 4) : Fin 4 :=
  if h : (x : ℕ) = 0 then y else r ⟨x - 1, by omega⟩ y

@[expose] def ColumnsInj (A : Fin 4 → Fin 4 → Fin 4) : Prop :=
  ∀ y x x', A x y = A x' y → x = x'

instance (A : Fin 4 → Fin 4 → Fin 4) : Decidable (ColumnsInj A) := by
  unfold ColumnsInj; infer_instance

@[expose] def Orth (A B : Fin 4 → Fin 4 → Fin 4) : Prop :=
  ∀ x y x' y', A x y = A x' y' → B x y = B x' y' → x = x' ∧ y = y'

instance (A B : Fin 4 → Fin 4 → Fin 4) : Decidable (Orth A B) := by
  unfold Orth; infer_instance

@[expose] def permOfImages (f : Fin 4 → Fin 4) (g : Fin 4 → Fin 4) (h1 : ∀ x, g (f x) = x)
    (h2 : ∀ x, f (g x) = x) : Perm (Fin 4) :=
  ⟨f, g, h1, h2⟩

@[expose] def rA : Fin 3 → Perm (Fin 4) :=
  ![permOfImages ![1, 0, 3, 2] ![1, 0, 3, 2] (by decide) (by decide),
    permOfImages ![2, 3, 0, 1] ![2, 3, 0, 1] (by decide) (by decide),
    permOfImages ![3, 2, 1, 0] ![3, 2, 1, 0] (by decide) (by decide)]

@[expose] def rB : Fin 3 → Perm (Fin 4) :=
  ![permOfImages ![2, 3, 0, 1] ![2, 3, 0, 1] (by decide) (by decide),
    permOfImages ![3, 2, 1, 0] ![3, 2, 1, 0] (by decide) (by decide),
    permOfImages ![1, 0, 3, 2] ![1, 0, 3, 2] (by decide) (by decide)]

@[expose] def rC : Fin 3 → Perm (Fin 4) :=
  ![permOfImages ![3, 2, 1, 0] ![3, 2, 1, 0] (by decide) (by decide),
    permOfImages ![1, 0, 3, 2] ![1, 0, 3, 2] (by decide) (by decide),
    permOfImages ![2, 3, 0, 1] ![2, 3, 0, 1] (by decide) (by decide)]

@[expose] def MolsLevel4 (r₂ r₃ : Fin 3 → Perm (Fin 4)) : Prop :=
  ∀ r₄ : Fin 3 → Perm (Fin 4), ColumnsInj (latinSq r₄) → Orth (latinSq r₂) (latinSq r₄) →
    Orth (latinSq r₃) (latinSq r₄) →
    (r₂ = rA ∧ r₃ = rB ∧ r₄ = rC) ∨ (r₂ = rA ∧ r₃ = rC ∧ r₄ = rB)

instance (r₂ r₃ : Fin 3 → Perm (Fin 4)) : Decidable (MolsLevel4 r₂ r₃) := by
  unfold MolsLevel4; infer_instance

@[expose] def MolsLevel3 (r₂ : Fin 3 → Perm (Fin 4)) : Prop :=
  ∀ r₃ : Fin 3 → Perm (Fin 4), ColumnsInj (latinSq r₃) → Orth (latinSq r₂) (latinSq r₃) →
    MolsLevel4 r₂ r₃

instance (r₂ : Fin 3 → Perm (Fin 4)) : Decidable (MolsLevel3 r₂) := by
  unfold MolsLevel3; infer_instance

@[expose] def MolsLevel2 : Prop :=
  ∀ r₂ : Fin 3 → Perm (Fin 4), (∀ x : Fin 3, r₂ x 0 = x.succ) → ColumnsInj (latinSq r₂) →
    MolsLevel3 r₂

instance : Decidable MolsLevel2 := by
  unfold MolsLevel2; infer_instance

end CFSG.ComponentClassification.WittDesign
