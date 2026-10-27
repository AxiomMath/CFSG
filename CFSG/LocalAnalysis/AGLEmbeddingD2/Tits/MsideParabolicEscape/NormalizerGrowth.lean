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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open scoped Pointwise

theorem exists_mem_normalizer_of_lt {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E P : Subgroup G} (hP : IsPGroup p P) (hEP : E < P) :
    ∃ x ∈ P, x ∈ Subgroup.normalizer (E : Set G) ∧ x ∉ E := by
  haveI : Group.IsNilpotent ↥P := IsPGroup.isNilpotent hP
  have hnc : NormalizerCondition ↥P := normalizerCondition_of_isNilpotent
  have hlt : E.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have : P ≤ E := by
      intro x hx
      have : (⟨x, hx⟩ : ↥P) ∈ E.subgroupOf P := by rw [h]; trivial
      exact this
    exact absurd hEP (not_lt_of_ge this)
  have := hnc _ hlt
  obtain ⟨y, hyN, hyH⟩ := Set.exists_of_ssubset this
  refine ⟨(y : G), y.2, ?_, fun h => hyH h⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hy' : y⁻¹ ∈ Subgroup.normalizer ((E.subgroupOf P : Subgroup ↥P) : Set ↥P) :=
    Subgroup.inv_mem _ hyN
  constructor
  · intro hg
    have hgP : g ∈ P := hEP.le hg
    have := (Subgroup.mem_normalizer_iff.mp hyN ⟨g, hgP⟩).mp hg
    exact this
  · intro hg
    have hgP : (y : G) * g * (y : G)⁻¹ ∈ P := hEP.le hg
    have h2 := (Subgroup.mem_normalizer_iff.mp hy' ⟨(y : G) * g * (y : G)⁻¹, hgP⟩).mp hg
    have : (y⁻¹ : ↥P) * ⟨(y : G) * g * (y : G)⁻¹, hgP⟩ * y⁻¹⁻¹ = ⟨g, by
      have := P.mul_mem (P.mul_mem (P.inv_mem y.2) hgP) y.2
      simpa [mul_assoc] using this⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [this] at h2
    exact h2

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
