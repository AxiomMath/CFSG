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

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem normal_subgroup_sylow_intersection (prime : ℕ) [Fact (Nat.Prime prime)]
    (normal : Subgroup G) [normal.Normal] (sylow : Sylow prime G) :
    ∃ relative : Sylow prime normal, (relative : Subgroup normal) =
      (sylow : Subgroup G).subgroupOf normal := by
  let intersection := (sylow : Subgroup G).subgroupOf normal
  have hintersectionP : IsPGroup prime intersection := sylow.isPGroup'.comap_subtype
  obtain ⟨relative, hrelative⟩ := hintersectionP.exists_le_sylow
  let mapped := (relative : Subgroup normal).map normal.subtype
  have hmappedP : IsPGroup prime mapped := relative.isPGroup'.map normal.subtype
  obtain ⟨overgroup, hovergroup⟩ := hmappedP.exists_le_sylow
  obtain ⟨actor, hactor⟩ := MulAction.exists_smul_eq G overgroup sylow
  have hconjugateSylow : (overgroup : Subgroup G).map (MulAut.conj actor).toMonoidHom =
      (sylow : Subgroup G) := by
    rw [← hactor, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  let conjugated := mapped.map (MulAut.conj actor).toMonoidHom
  have hconjugatedSylow : conjugated ≤ (sylow : Subgroup G) := by
    rw [← hconjugateSylow]
    exact Subgroup.map_mono hovergroup
  have hconjugatedNormal : conjugated ≤ normal := by
    intro element hmem
    obtain ⟨original, horiginal, rfl⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨relativeElement, _, rfl⟩ := Subgroup.mem_map.mp horiginal
    exact (inferInstance : normal.Normal).conj_mem relativeElement relativeElement.property actor
  have hle : conjugated ≤ (sylow : Subgroup G) ⊓ normal :=
    le_inf hconjugatedSylow hconjugatedNormal
  have hcardConjugated : Nat.card conjugated = Nat.card (relative : Subgroup normal) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj actor).injective,
      Subgroup.card_map_of_injective normal.subtype_injective]
  have hcardIntersection : Nat.card ↥((sylow : Subgroup G) ⊓ normal) = Nat.card intersection := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective normal.subtype_injective]
  have hcardGe : Nat.card (relative : Subgroup normal) ≤ Nat.card intersection := by
    have hdiv := Subgroup.card_dvd_of_le hle
    rw [hcardConjugated, hcardIntersection] at hdiv
    exact Nat.le_of_dvd Nat.card_pos hdiv
  exact ⟨relative, (Subgroup.eq_of_le_of_card_ge hrelative hcardGe).symm⟩

end CFSG.DisconnectedInvolutionGraph.Helpers
