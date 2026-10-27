module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorConjugation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot

open CFSG
open CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

universe u

variable {G : Type u} [Group G]

theorem centralizer_zpowers_eq_singleton (g : G) :
    Subgroup.centralizer (Subgroup.zpowers g : Set G) =
      Subgroup.centralizer ({g} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem normalized_common_fixed_map (J V : Subgroup G)
    (hV : V ≤ Subgroup.normalizer (J : Set G)) :
    let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
    (fixedPointSubgroup V J).map J.subtype = J ⊓ Subgroup.centralizer (V : Set G) := by
  let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro a ha
    have hf : (⟨a, ha⟩ : V) • y = y := hy ⟨a, ha⟩
    have hconj : a * (y : G) * a⁻¹ = y := congrArg Subtype.val hf
    exact mul_inv_eq_iff_eq_mul.mp hconj
  · rintro ⟨hxJ, hxC⟩
    refine ⟨⟨x, hxJ⟩, ?_, rfl⟩
    change ∀ a : V, a • (⟨x, hxJ⟩ : J) = ⟨x, hxJ⟩
    intro a
    apply Subtype.ext
    change (a : G) * x * (a : G)⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_iff.mp hxC a a.property)

theorem normalized_tCentralizer_invariant (J V : Subgroup G)
    (hV : V ≤ Subgroup.normalizer (J : Set G)) (t : G)
    (htV : t ∈ Subgroup.centralizer (V : Set G)) :
    let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
    CFSG.IsInvariant V J ((Subgroup.centralizer ({t} : Set G)).subgroupOf J) := by
  let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
  constructor
  intro a x
  change ((x : G) ∈ Subgroup.centralizer ({t} : Set G)) ↔
    (((a • x : J) : G) ∈ Subgroup.centralizer ({t} : Set G))
  rw [normalizedSubgroupAction_smul_coe]
  have ha : Commute (a : G) t := Subgroup.mem_centralizer_iff.mp htV a a.property
  constructor
  · intro hx
    have hx' : Commute (x : G) t := Subgroup.mem_centralizer_singleton_iff.mp hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((ha.mul_left hx').mul_left ha.inv_left)
  · intro hx
    have hx' : Commute ((a : G) * (x : G) * (a : G)⁻¹) t :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    have hback := (ha.inv_left.mul_left hx').mul_left ha
    have heq : (a : G)⁻¹ * ((a : G) * (x : G) * (a : G)⁻¹) * a = x := by group
    rw [heq] at hback
    exact Subgroup.mem_centralizer_singleton_iff.mpr hback

theorem normalized_common_fixed_relative_index (J V : Subgroup G)
    (hV : V ≤ Subgroup.normalizer (J : Set G)) (t : G) :
    let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
    ((Subgroup.centralizer ({t} : Set G)).subgroupOf J).relIndex
        (fixedPointSubgroup V J) =
      (Subgroup.centralizer ({t} : Set G)).relIndex
        (J ⊓ Subgroup.centralizer (V : Set G)) := by
  let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
  change ((Subgroup.centralizer ({t} : Set G)).subgroupOf J).relIndex
      (fixedPointSubgroup V J) =
    (Subgroup.centralizer ({t} : Set G)).relIndex (J ⊓ Subgroup.centralizer (V : Set G))
  have hfixed : fixedPointSubgroup V J =
      (J ⊓ Subgroup.centralizer (V : Set G)).subgroupOf J := by
    apply Subgroup.map_injective J.subtype_injective
    rw [normalized_common_fixed_map J V hV,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  rw [hfixed]
  exact Subgroup.relIndex_subgroupOf inf_le_left

theorem normalized_actor_fixed_relative_index (J V : Subgroup G)
    (hV : V ≤ Subgroup.normalizer (J : Set G)) (t : G) (a : V) :
    let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
    ((Subgroup.centralizer ({t} : Set G)).subgroupOf J).relIndex
        (actorFixedSubgroup (I := J) a) =
      (Subgroup.centralizer ({t} : Set G)).relIndex
        (J ⊓ Subgroup.centralizer ({(a : G)} : Set G)) := by
  let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
  change ((Subgroup.centralizer ({t} : Set G)).subgroupOf J).relIndex
      (actorFixedSubgroup (I := J) a) =
    (Subgroup.centralizer ({t} : Set G)).relIndex
      (J ⊓ Subgroup.centralizer ({(a : G)} : Set G))
  have hfixed : actorFixedSubgroup (I := J) a =
      (J ⊓ Subgroup.centralizer ({(a : G)} : Set G)).subgroupOf J := by
    apply Subgroup.map_injective J.subtype_injective
    rw [normalized_fixed_map J V hV a,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  rw [hfixed]
  exact Subgroup.relIndex_subgroupOf inf_le_left

end CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot
