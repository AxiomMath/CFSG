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
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

theorem le_of_perfect_of_card_two_pow {G : Type*} [Group G] [Finite G] {N H R : Subgroup G}
    (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) (k : ℕ)
    (hcard : Nat.card H = 2 ^ k * Nat.card N) (hRH : R ≤ H) (hR : ⁅R, R⁆ = R) : R ≤ N := by
  let N' : Subgroup H := N.subgroupOf H
  let R' : Subgroup H := R.subgroupOf H
  haveI hN'normal : N'.Normal := hN
  have hN'card : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  haveI : Nonempty N := ⟨1⟩
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hQcard : Nat.card (H ⧸ N') = 2 ^ k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
    rw [hN'card] at h1
    exact Nat.eq_of_mul_eq_mul_right hNpos (by rw [← h1, hcard])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent (H ⧸ N') :=
    IsPGroup.isNilpotent (p := 2) (IsPGroup.of_card (p := 2) (n := k) hQcard)
  haveI : Group.IsSolvable (H ⧸ N') := IsNilpotent.to_isSolvable
  have hR'map : R'.map H.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRH
  have hN'map : N'.map H.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNH
  have hR'perfect : Group.IsPerfect R' := by
    rw [Subgroup.isPerfect_iff]
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_commutator, hR'map, hR]
  have hSbot : R'.map (QuotientGroup.mk' N') = ⊥ := by
    by_contra hne
    haveI : Nontrivial (R'.map (QuotientGroup.mk' N')) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    haveI : Group.IsPerfect (R'.map (QuotientGroup.mk' N')) :=
      hR'perfect.map (QuotientGroup.mk' N')
    exact Group.IsPerfect.not_isSolvable (R'.map (QuotientGroup.mk' N')) inferInstance
  have hR'N' : R' ≤ N' := by
    have h := (Subgroup.map_eq_bot_iff R' (f := QuotientGroup.mk' N')).mp hSbot
    rwa [QuotientGroup.ker_mk'] at h
  simpa [hR'map, hN'map] using Subgroup.map_mono (f := H.subtype) hR'N'

end CFSG.EvenSporadicStandard.M12Std.PropA
