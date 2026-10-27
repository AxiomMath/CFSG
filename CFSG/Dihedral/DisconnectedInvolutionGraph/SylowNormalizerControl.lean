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

theorem sylow_inheritance_of_normalizer_le (prime : ℕ) [Fact (Nat.Prime prime)]
    (subgroup : Subgroup G) (sylow : Sylow prime subgroup)
    (hnormalizer : Subgroup.normalizer
      (((sylow : Subgroup subgroup).map subgroup.subtype : Subgroup G) : Set G) ≤ subgroup) :
    ∃ ambient : Sylow prime G,
      (sylow : Subgroup subgroup).map subgroup.subtype = (ambient : Subgroup G) := by
  let smaller : Subgroup G := (sylow : Subgroup subgroup).map subgroup.subtype
  obtain ⟨ambient, hcomap⟩ := sylow.exists_comap_subtype_eq
  have hmap : (subgroup.comap (ambient : Subgroup G).subtype).map
      (ambient : Subgroup G).subtype = smaller := by
    rw [Subgroup.map_comap_eq, Subgroup.subtype_range]
    change (ambient : Subgroup G) ⊓ subgroup = (sylow : Subgroup subgroup).map subgroup.subtype
    rw [← hcomap, Subgroup.map_comap_eq, Subgroup.subtype_range, inf_comm]
  let within : Subgroup (ambient : Subgroup G) := subgroup.comap (ambient : Subgroup G).subtype
  have hselfNormalizer : Subgroup.normalizer (within : Set (ambient : Subgroup G)) = within := by
    apply le_antisymm
    · intro element hmem
      have hmapped := Subgroup.le_normalizer_map (ambient : Subgroup G).subtype
        (Subgroup.mem_map.mpr ⟨element, hmem, rfl⟩)
      change (element : G) ∈ Subgroup.normalizer
        (((within.map (ambient : Subgroup G).subtype) : Subgroup G) : Set G) at hmapped
      change (element : G) ∈ subgroup
      rw [show within.map (ambient : Subgroup G).subtype = smaller from hmap] at hmapped
      exact hnormalizer hmapped
    · exact Subgroup.le_normalizer
  have _ : Group.IsNilpotent (ambient : Subgroup G) := ambient.isPGroup'.isNilpotent
  have htop : within = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent within hselfNormalizer
  have hambientLe : (ambient : Subgroup G) ≤ subgroup := by
    intro element hmem
    have hwithin : (⟨element, hmem⟩ : (ambient : Subgroup G)) ∈ within := by
      rw [htop]
      trivial
    exact hwithin
  refine ⟨ambient, ?_⟩
  change smaller = (ambient : Subgroup G)
  rw [← hmap, Subgroup.map_comap_eq, Subgroup.subtype_range, inf_eq_left.mpr hambientLe]

end CFSG.DisconnectedInvolutionGraph.Helpers
