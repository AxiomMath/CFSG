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

variable {G : Type*} [Group G] [Finite G] [IsCyclic G]

theorem cyclic_subgroup_le_of_card_dvd (smaller larger : Subgroup G)
    (hdiv : Nat.card smaller ∣ Nat.card larger) : smaller ≤ larger := by
  let _ : IsMulCommutative G := inferInstance
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := mul_comm' }
  let roots : Subgroup G := (powMonoidHom (Nat.card larger)).ker
  have hlargerLe : larger ≤ roots := by
    intro element hmem
    change element ^ Nat.card larger = 1
    exact orderOf_dvd_iff_pow_eq_one.mp (larger.orderOf_dvd_natCard hmem)
  have hrootsCard : Nat.card roots = Nat.card larger := by
    rw [IsCyclic.card_powMonoidHom_ker G, Nat.gcd_eq_right
      larger.card_subgroup_dvd_card]
  have hrootsEq : roots = larger :=
    (Subgroup.eq_of_le_of_card_ge hlargerLe (by rw [hrootsCard])).symm
  rw [← hrootsEq]
  intro element hmem
  change element ^ Nat.card larger = 1
  exact orderOf_dvd_iff_pow_eq_one.mp ((smaller.orderOf_dvd_natCard hmem).trans hdiv)

theorem cyclic_pgroup_subgroups_comparable (prime : ℕ) [Fact (Nat.Prime prime)]
    (hpgroup : IsPGroup prime G) (first second : Subgroup G) :
    first ≤ second ∨ second ≤ first := by
  obtain ⟨firstExponent, hfirst⟩ := IsPGroup.iff_card.mp (hpgroup.to_subgroup first)
  obtain ⟨secondExponent, hsecond⟩ := IsPGroup.iff_card.mp (hpgroup.to_subgroup second)
  rcases le_total firstExponent secondExponent with hle | hle
  · left
    apply cyclic_subgroup_le_of_card_dvd
    rw [hfirst, hsecond]
    exact pow_dvd_pow _ hle
  · right
    apply cyclic_subgroup_le_of_card_dvd
    rw [hfirst, hsecond]
    exact pow_dvd_pow _ hle

end CFSG.DisconnectedInvolutionGraph.Helpers
