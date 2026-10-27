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
public import Mathlib.GroupTheory.Transfer
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

namespace CFSG.TwoRankLowerBound.Helpers

theorem hom_to_two_group_eq_one_of_odd_order {source target : Type*}
    [Group source] [Group target] (htwo : IsPGroup 2 target)
    (homomorphism : source →* target) (element : source) (hodd : Odd (orderOf element)) :
    homomorphism element = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hdiv := htwo.dvd_orderOf hne
  have hoddimage := hodd.of_dvd_nat (orderOf_map_dvd homomorphism element)
  exact (Nat.not_even_iff_odd.mpr hoddimage) (even_iff_two_dvd.mpr hdiv)

theorem exists_characteristic_odd_complement_of_cyclic_sylow_two {G : Type*}
    [Group G] [Finite G] (sylow : Sylow 2 G) (hcyclic : IsCyclic (sylow : Subgroup G))
    (heven : Even (Nat.card G)) :
    ∃ kernel : Subgroup G, kernel.Characteristic ∧ Odd (Nat.card kernel) ∧
      kernel.IsComplement' (sylow : Subgroup G) ∧
      ∀ element : G, element ∈ kernel ↔ Odd (orderOf element) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnormalizer := IsCyclic.normalizer_le_centralizer
    ((Nat.minFac_eq_two_iff _).mpr (even_iff_two_dvd.mp heven)) hcyclic
  let transfer : G →* (sylow : Subgroup G) := MonoidHom.transferSylow sylow hnormalizer
  have hcomplement := MonoidHom.ker_transferSylow_isComplement' sylow hnormalizer
  change transfer.ker.IsComplement' (sylow : Subgroup G) at hcomplement
  have hodd : Odd (Nat.card transfer.ker) := by
    rw [← hcomplement.index_eq_card]
    apply Nat.not_even_iff_odd.mp
    intro hevenindex
    exact sylow.not_dvd_index (even_iff_two_dvd.mp hevenindex)
  have hmembership : ∀ element : G, element ∈ transfer.ker ↔ Odd (orderOf element) := by
    intro element
    constructor
    · intro hmember
      exact hodd.of_dvd_nat (transfer.ker.orderOf_dvd_natCard hmember)
    · intro helement
      exact hom_to_two_group_eq_one_of_odd_order sylow.isPGroup' transfer element helement
  have hcharacteristic : transfer.ker.Characteristic := by
    constructor
    intro automorphism
    ext element
    change automorphism element ∈ transfer.ker ↔ element ∈ transfer.ker
    rw [hmembership, hmembership, automorphism.orderOf_eq]
  exact ⟨transfer.ker, hcharacteristic, hodd, hcomplement, hmembership⟩

end CFSG.TwoRankLowerBound.Helpers
