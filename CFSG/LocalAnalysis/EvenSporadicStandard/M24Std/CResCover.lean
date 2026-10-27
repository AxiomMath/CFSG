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

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup
open scoped commutatorElement

theorem exists_perfect_cover {Y : Type} [Group Y] [Finite Y] (O : Subgroup Y) [O.Normal]
    (L : Subgroup (Y ⧸ O)) [L.Normal] (hL : commutator L = ⊤) :
    ∃ U : Subgroup Y, U.Normal ∧ commutator U = ⊤ ∧
      ∃ q : U →* L, Function.Surjective q ∧
        ∀ u : U, ((q u : L) : Y ⧸ O) = QuotientGroup.mk (u : Y) := by
  classical
  let P : Subgroup Y := L.comap (QuotientGroup.mk' O)
  have hPn : P.Normal := Normal.comap inferInstance _
  let q₀ : P →* L := ((QuotientGroup.mk' O).comp P.subtype).codRestrict L fun p => p.2
  have hq₀ : Function.Surjective q₀ := by
    intro l
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (l : Y ⧸ O)
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    show QuotientGroup.mk' O y ∈ L
    rw [QuotientGroup.mk'_apply, hy]
    exact l.2
  have hDtop : ∀ n, (derivedSeries P n).map q₀ = ⊤ := by
    intro n
    rw [map_derivedSeries_eq hq₀ n]
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih]; exact hL
  obtain ⟨N, hN⟩ := (wellFounded_lt (α := ℕ)).has_min
    (Set.range fun n => Nat.card (derivedSeries P n)) ⟨_, ⟨0, rfl⟩⟩
  obtain ⟨⟨n₀, rfl⟩, hmin⟩ := hN
  set D : Subgroup P := derivedSeries P n₀ with hD
  have hle : derivedSeries P (n₀ + 1) ≤ D := by
    rw [derivedSeries_succ, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hge : Nat.card D ≤ Nat.card (derivedSeries P (n₀ + 1)) := by
    by_contra hlt
    exact hmin _ ⟨n₀ + 1, rfl⟩ (not_le.1 hlt)
  have hstab : derivedSeries P (n₀ + 1) = D := Subgroup.eq_of_le_of_card_ge hle hge
  have hDD : ⁅D, D⁆ = D := by
    rw [← derivedSeries_succ]
    exact hstab
  let U : Subgroup Y := D.map P.subtype
  have hUP : U ≤ P := by
    rintro _ ⟨p, _, rfl⟩
    exact p.2
  have hUn : U.Normal := by
    refine ⟨fun u hu y => ?_⟩
    obtain ⟨p, hp, rfl⟩ := hu
    have hmap : D.map (MulAut.conjNormal (H := P) y).toMonoidHom = D := by
      rw [hD]
      exact map_derivedSeries_eq (MulAut.conjNormal (H := P) y).surjective n₀
    have hmem : MulAut.conjNormal (H := P) y p ∈ D := by
      rw [← hmap]
      exact mem_map_of_mem _ hp
    exact ⟨_, hmem, by simp [MulAut.conjNormal_apply]⟩
  have hUperf : commutator U = ⊤ := by
    have h1 : ⁅U, U⁆ = U := by
      show ⁅D.map P.subtype, D.map P.subtype⁆ = D.map P.subtype
      rw [← Subgroup.map_commutator, hDD]
    exact ((Subgroup.isPerfect_iff).2 h1).commutator_eq_top
  refine ⟨U, hUn, hUperf, ((QuotientGroup.mk' O).comp U.subtype).codRestrict L
    fun u => hUP u.2, ?_, fun u => rfl⟩
  intro l
  have hl : l ∈ D.map q₀ := by rw [hD, hDtop n₀]; exact mem_top l
  obtain ⟨p, hp, hpl⟩ := hl
  exact ⟨⟨p.1, mem_map_of_mem _ hp⟩, Subtype.ext (congrArg Subtype.val hpl)⟩

end CFSG.EvenSporadicStandard.M24Std
