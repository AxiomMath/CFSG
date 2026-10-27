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
public import Mathlib.Order.CompletePartialOrder
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

public noncomputable section

namespace CFSG.LieType.Chevalley.RootWeight

open scoped RealInnerProductSpace

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[expose] def weightFiltration (Ω : Finset E) (Vχ : E → Submodule K V) (l : E) (c : ℝ) :
    Submodule K V :=
  ⨆ (χ : E) (_ : χ ∈ Ω) (_ : c ≤ ⟪χ, l⟫), Vχ χ

variable {Ω : Finset E} {Vχ : E → Submodule K V}

theorem le_weightFiltration {l : E} {c : ℝ} {χ : E} (hχ : χ ∈ Ω) (hc : c ≤ ⟪χ, l⟫) :
    Vχ χ ≤ weightFiltration Ω Vχ l c :=
  le_iSup₂_of_le χ hχ (le_iSup_of_le hc le_rfl)

theorem weightFiltration_le_iff {l : E} {c : ℝ} {W : Submodule K V} :
    weightFiltration Ω Vχ l c ≤ W ↔ ∀ χ ∈ Ω, c ≤ ⟪χ, l⟫ → Vχ χ ≤ W := by
  simp only [weightFiltration, iSup_le_iff]

theorem weightFiltration_antitone (l : E) : Antitone (weightFiltration Ω Vχ l) :=
  fun _ _ hcc' => weightFiltration_le_iff.2 fun _ hχ hc => le_weightFiltration hχ (hcc'.trans hc)

end CFSG.LieType.Chevalley.RootWeight
