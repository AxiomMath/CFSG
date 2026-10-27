module

public import CFSG.Foundations.MaxCardThompson
import CFSG.Foundations.MaxOrderThompson
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

namespace CFSG.OrderReductions.ThompsonCenter

@[expose, reducible] def MaximumOrderAbelian (group : Type*) [Group group] (subgroup : Subgroup group) :
    Prop :=
  CFSG.IsMaxCardAbelian subgroup

@[expose, reducible] def thompson (group : Type*) [Group group] : Subgroup group :=
  CFSG.maxCardThompson group

@[expose, reducible] def thompsonCenter (group : Type*) [Group group] : Subgroup group :=
  CFSG.maxCardZJ group

private theorem thompson_eq_canonical (group : Type*) [Group group] [Finite group] :
    thompson group = CFSG.orderThompson group :=
  CFSG.maxCardThompson_eq_orderThompson

private theorem thompsonCenter_eq_canonical (group : Type*) [Group group] [Finite group] :
    thompsonCenter group = CFSG.orderZJ group :=
  CFSG.maxCardZJ_eq_orderZJ

theorem exists_maximum_order_abelian (group : Type*) [Group group] [Finite group] :
    ∃ subgroup : Subgroup group, MaximumOrderAbelian group subgroup := by
  obtain ⟨subgroup, member⟩ := CFSG.maxOrderAbelianFamily_nonempty (G := group)
  exact ⟨subgroup, CFSG.isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mpr member⟩

theorem maximum_order_abelian_map {source target : Type*} [Group source] [Group target]
    (equivalence : source ≃* target) (subgroup : Subgroup source)
    (maximal : MaximumOrderAbelian source subgroup) :
    MaximumOrderAbelian target (subgroup.map equivalence.toMonoidHom) :=
  CFSG.IsMaxCardAbelian.map_mulEquiv equivalence maximal

theorem thompson_map_le {source target : Type*} [Group source] [Group target]
    (equivalence : source ≃* target) :
    (thompson source).map equivalence.toMonoidHom ≤ thompson target :=
  CFSG.maxCardThompson_map_le equivalence

theorem thompson_map_eq {source target : Type*} [Group source] [Group target]
    (equivalence : source ≃* target) :
    (thompson source).map equivalence.toMonoidHom = thompson target :=
  CFSG.maxCardThompson_map_mulEquiv equivalence

instance thompson_characteristic (group : Type*) [Group group] : (thompson group).Characteristic :=
  CFSG.maxCardThompson_characteristic

theorem center_map_eq {source target : Type*} [Group source] [Group target]
    (equivalence : source ≃* target) :
    (Subgroup.center source).map equivalence.toMonoidHom = Subgroup.center target := by
  apply le_antisymm
  · rintro element ⟨original, original_center, image_eq⟩
    rw [← image_eq]
    apply Subgroup.mem_center_iff.mpr
    intro other
    change other * equivalence original = equivalence original * other
    have commutes := congrArg equivalence (Subgroup.mem_center_iff.mp original_center (equivalence.symm other))
    simpa only [map_mul, equivalence.apply_symm_apply] using commutes
  · intro element element_center
    apply Subgroup.mem_map.mpr
    refine ⟨equivalence.symm element, Subgroup.mem_center_iff.mpr ?_, equivalence.apply_symm_apply element⟩
    intro other
    apply equivalence.injective
    simpa only [map_mul, equivalence.apply_symm_apply] using Subgroup.mem_center_iff.mp element_center (equivalence other)

theorem thompsonCenter_map_eq {source target : Type*} [Group source] [Group target]
    (equivalence : source ≃* target) :
    (thompsonCenter source).map equivalence.toMonoidHom = thompsonCenter target :=
  CFSG.maxCardZJ_map_mulEquiv equivalence

instance thompsonCenter_characteristic (group : Type*) [Group group] :
    (thompsonCenter group).Characteristic :=
  CFSG.maxCardZJ_characteristic

theorem thompsonCenter_le (group : Type*) [Group group] : thompsonCenter group ≤ thompson group :=
  Subgroup.map_subtype_le _

theorem thompson_eq_top_of_abelian (group : Type*) [Group group] [Finite group] [IsMulCommutative group] :
    thompson group = ⊤ :=
  (thompson_eq_canonical group).trans CFSG.orderThompson_eq_top

theorem thompsonCenter_eq_top_of_abelian (group : Type*) [Group group] [Finite group] [IsMulCommutative group] :
    thompsonCenter group = ⊤ :=
  (thompsonCenter_eq_canonical group).trans CFSG.orderZJ_eq_top

theorem maximum_order_abelian_contains_center {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (maximal : MaximumOrderAbelian group subgroup) :
    Subgroup.center group ≤ subgroup :=
  CFSG.center_le_of_mem_maxOrderAbelianFamily
    (CFSG.isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mp maximal)

theorem center_le_thompson {group : Type*} [Group group] [Finite group] :
    Subgroup.center group ≤ thompson group :=
  (thompson_eq_canonical group).symm ▸ CFSG.center_le_orderThompson

theorem center_le_thompsonCenter {group : Type*} [Group group] [Finite group] :
    Subgroup.center group ≤ thompsonCenter group :=
  (thompsonCenter_eq_canonical group).symm ▸ CFSG.center_le_orderZJ_of_finite

theorem thompsonCenter_nontrivial_of_prime_group {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group) [Nontrivial group] :
    thompsonCenter group ≠ ⊥ :=
  (thompsonCenter_eq_canonical group).symm ▸ CFSG.orderZJ_ne_bot_of_isPGroup Fact.out prime_group

theorem maximum_order_abelian_subgroupOf {group : Type*} [Group group] [Finite group]
    (subgroup overgroup : Subgroup group) (contains : subgroup ≤ overgroup)
    (maximal : MaximumOrderAbelian group subgroup) :
    MaximumOrderAbelian overgroup (subgroup.subgroupOf overgroup) :=
  CFSG.IsMaxCardAbelian.subgroupOf maximal contains

theorem maximum_order_abelian_image_of_contains_maximum {group : Type*} [Group group] [Finite group]
    (overgroup maximum : Subgroup group) (contains : maximum ≤ overgroup)
    (ambient_maximal : MaximumOrderAbelian group maximum)
    (subgroup : Subgroup overgroup) (maximal : MaximumOrderAbelian overgroup subgroup) :
    MaximumOrderAbelian group (subgroup.map overgroup.subtype) :=
  CFSG.IsMaxCardAbelian.map_subtype ambient_maximal contains maximal

theorem thompsonCenter_le_maximum_order_abelian {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (maximal : MaximumOrderAbelian group subgroup) :
    thompsonCenter group ≤ subgroup :=
  (thompsonCenter_eq_canonical group).symm ▸ CFSG.orderZJ_le_of_mem_maxOrderAbelianFamily
    (CFSG.isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mp maximal)

theorem thompsonCenter_mem_iff {group : Type*} [Group group] [Finite group] (element : group) :
    element ∈ thompsonCenter group ↔ ∀ subgroup : Subgroup group,
      MaximumOrderAbelian group subgroup → element ∈ subgroup := by
  rw [thompsonCenter_eq_canonical, CFSG.mem_orderZJ_iff]
  exact forall_congr' fun _ => imp_congr_left CFSG.isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.symm

theorem thompsonCenter_eq_intersection {group : Type*} [Group group] [Finite group] :
    thompsonCenter group = sInf {subgroup : Subgroup group | MaximumOrderAbelian group subgroup} := by
  rw [thompsonCenter_eq_canonical, CFSG.orderZJ_eq_sInf, ← CFSG.setOf_isMaxCardAbelian_eq]

theorem thompsonCenter_le_overgroup_of_contains_maximum {group : Type*} [Group group] [Finite group]
    (overgroup maximum : Subgroup group) (contains : maximum ≤ overgroup)
    (maximal : MaximumOrderAbelian group maximum) :
    thompsonCenter group ≤ (thompsonCenter overgroup).map overgroup.subtype := by
  rw [thompsonCenter_eq_canonical, thompsonCenter_eq_canonical]
  exact CFSG.orderZJ_le_ambientOrderZJ
    (CFSG.isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mp maximal) contains

end CFSG.OrderReductions.ThompsonCenter
