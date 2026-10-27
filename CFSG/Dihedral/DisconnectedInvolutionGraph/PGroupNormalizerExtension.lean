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

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem pgroup_strict_normalizer_extension (prime : ℕ) [Fact (Nat.Prime prime)]
    (smaller larger : Subgroup G) (hpgroup : IsPGroup prime larger)
    (hproper : smaller < larger) :
    ∃ extension : Subgroup G, smaller < extension ∧ IsPGroup prime extension ∧
      extension ≤ larger ⊓ Subgroup.normalizer (smaller : Set G) := by
  let within := smaller.subgroupOf larger
  let normalizer := Subgroup.normalizer (within : Set larger)
  let extension := normalizer.map larger.subtype
  have hmap : within.map larger.subtype = smaller :=
    Subgroup.map_subgroupOf_eq_of_le hproper.le
  have _ : Group.IsNilpotent larger := hpgroup.isNilpotent
  have hstrict : within < normalizer := by
    apply lt_of_le_of_ne Subgroup.le_normalizer
    intro heq
    have htop : within = ⊤ :=
      normalizerCondition_iff_only_full_group_self_normalizing.mp
        Group.normalizerCondition_of_isNilpotent within heq.symm
    have hequal : smaller = larger := by
      apply le_antisymm hproper.le
      intro element hmem
      have hwithin : (⟨element, hmem⟩ : larger) ∈ within := by
        rw [htop]
        trivial
      exact hwithin
    exact hproper.ne hequal
  refine ⟨extension, ?_, (hpgroup.to_subgroup normalizer).map larger.subtype, ?_⟩
  · rw [← hmap]
    exact Subgroup.map_subtype_lt_map_subtype.mpr hstrict
  · refine le_inf (Subgroup.map_subtype_le normalizer) ?_
    have hnormalizes := Subgroup.le_normalizer_map larger.subtype (H := within)
    rw [hmap] at hnormalizes
    exact hnormalizes

end CFSG.DisconnectedInvolutionGraph.Helpers
