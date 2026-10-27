module

public import CFSG.Assembly.OrderReductions.GlaubermanReplacement
public import CFSG.Assembly.OrderReductions.PrimeQuotientFrattini
public import CFSG.Assembly.OrderReductions.ThompsonGrowthCore
public import CFSG.Assembly.OrderReductions.ThompsonNormalizer

public section

namespace CFSG.OrderReductions.ThompsonGrowthTrap

open CFSG.OrderReductions.ThompsonCenter CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.PrimeCore
open CFSG.OrderReductions.PrimeQuotientFrattini CFSG.OrderReductions.ThompsonGrowthCore

attribute [local instance] commutatorElement

theorem normalClosure_le_of_factorization {group : Type*} [Group group]
    (subgroup trap : Subgroup group) (contains : subgroup ≤ trap)
    (factorization : Subgroup.centralizer (Subgroup.normalClosure (subgroup : Set group) : Set group) ⊔
      Subgroup.normalizer (trap : Set group) = ⊤) :
    Subgroup.normalClosure (subgroup : Set group) ≤ trap := by
  apply (Subgroup.closure_le _).mpr
  intro value value_mem
  obtain ⟨original, original_mem, conjugate⟩ := Group.mem_conjugatesOfSet_iff.mp value_mem
  obtain ⟨conjugator, equal⟩ := isConj_iff.mp conjugate
  obtain ⟨centralizer, centralizer_mem, normalizer, normalizer_mem, product_eq⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (factorization ▸ Subgroup.mem_top conjugator)
  have conjugated_trap := (Subgroup.mem_normalizer_iff.mp normalizer_mem original).mp (contains original_mem)
  have conjugated_closure := Subgroup.Normal.conj_mem inferInstance original
    (Subgroup.le_normalClosure original_mem) normalizer
  have commutes := Subgroup.mem_centralizer_iff.mp centralizer_mem
    (normalizer * original * normalizer⁻¹) conjugated_closure
  rw [← equal, ← product_eq]
  have conjugate_eq : (centralizer * normalizer) * original * (centralizer * normalizer)⁻¹ =
      normalizer * original * normalizer⁻¹ := by
    calc
      (centralizer * normalizer) * original * (centralizer * normalizer)⁻¹ =
          centralizer * (normalizer * original * normalizer⁻¹) * centralizer⁻¹ := by group
      _ = (normalizer * original * normalizer⁻¹) * centralizer * centralizer⁻¹ := by rw [← commutes]
      _ = normalizer * original * normalizer⁻¹ := by group
  rwa [conjugate_eq]

theorem internal_commutator_central_of_ambient {group : Type*} [Group group]
    (subgroup : Subgroup group)
    (central : ⁅subgroup, subgroup⁆ ≤ Subgroup.centralizer (subgroup : Set group)) :
    commutator subgroup ≤ Subgroup.center subgroup := by
  intro element element_mem
  have image_mem : element.val ∈ ⁅subgroup, subgroup⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.mem_map.mpr ⟨element, element_mem, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro other
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (central image_mem) other.val other.property)

theorem ambient_commutator_central_of_internal {group : Type*} [Group group]
    (subgroup : Subgroup group) (central : commutator subgroup ≤ Subgroup.center subgroup) :
    ⁅subgroup, subgroup⁆ ≤ Subgroup.centralizer (subgroup : Set group) := by
  intro element element_mem
  rw [← Subgroup.map_subtype_commutator] at element_mem
  obtain ⟨original, original_mem, equal⟩ := Subgroup.mem_map.mp element_mem
  apply Subgroup.mem_centralizer_iff.mpr
  intro other other_mem
  have commutes := congrArg Subtype.val (Subgroup.mem_center_iff.mp (central original_mem) ⟨other, other_mem⟩)
  change other * original.val = original.val * other at commutes
  change original.val = element at equal
  rwa [equal] at commutes

theorem subgroupOf_commutator_central {group : Type*} [Group group]
    (subgroup ambient : Subgroup group) (contains : subgroup ≤ ambient)
    (central : commutator subgroup ≤ Subgroup.center subgroup) :
    commutator (subgroup.subgroupOf ambient) ≤ Subgroup.center (subgroup.subgroupOf ambient) := by
  have ambient_central := ambient_commutator_central_of_internal subgroup central
  apply internal_commutator_central_of_ambient
  intro element element_mem
  have mapped_mem : element.val ∈ ⁅subgroup, subgroup⁆ := by
    have mapped : element.val ∈ (⁅subgroup.subgroupOf ambient, subgroup.subgroupOf ambient⁆).map ambient.subtype :=
      Subgroup.mem_map.mpr ⟨element, element_mem, rfl⟩
    have image_eq : (⁅subgroup.subgroupOf ambient, subgroup.subgroupOf ambient⁆).map ambient.subtype =
        ⁅subgroup, subgroup⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le contains]
    rwa [image_eq] at mapped
  apply Subgroup.mem_centralizer_iff.mpr
  intro other other_mem
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (ambient_central mapped_mem) other.val other_mem)

theorem normalized_abelian_le_actionCore {group : Type*} [Group group]
    (prime : ℕ) (normal : Subgroup group) [normal.Normal]
    (stable : primeStable prime (conjugationAction normal))
    (subgroup : Subgroup group) [IsMulCommutative subgroup]
    (normalizes : normal ≤ Subgroup.normalizer (subgroup : Set group)) :
    subgroup ≤ actionCore prime (conjugationAction normal) := by
  intro actor actor_mem
  exact stable actor (abelian_normalized_quadratic subgroup normal normal le_rfl normalizes ⟨actor, actor_mem⟩)

theorem thompsonCenter_image_subgroupOf {group : Type*} [Group group]
    (subgroup ambient : Subgroup group) (contains : subgroup ≤ ambient) :
    ((thompsonCenter (subgroup.subgroupOf ambient)).map (subgroup.subgroupOf ambient).subtype).map ambient.subtype =
      (thompsonCenter subgroup).map subgroup.subtype := by
  let equivalence := Subgroup.subgroupOfEquivOfLe contains
  have image_eq := congrArg (Subgroup.map subgroup.subtype) (thompsonCenter_map_eq equivalence)
  rw [Subgroup.map_map] at image_eq
  have intertwines : subgroup.subtype.comp equivalence.toMonoidHom =
      ambient.subtype.comp (subgroup.subgroupOf ambient).subtype := by
    ext element
    rfl
  rwa [intertwines, ← Subgroup.map_map] at image_eq

theorem internal_derived_le_of_ambient {group : Type*} [Group group]
    (subgroup ambient : Subgroup group) (contains : subgroup ≤ ambient)
    (target : Subgroup ambient) (derived_le : ⁅subgroup, subgroup⁆ ≤ target.map ambient.subtype) :
    ⁅subgroup.subgroupOf ambient, subgroup.subgroupOf ambient⁆ ≤ target := by
  have mapped : (⁅subgroup.subgroupOf ambient, subgroup.subgroupOf ambient⁆).map ambient.subtype ≤ target.map ambient.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le contains]
    exact derived_le
  exact Subgroup.map_subtype_le_map_subtype.mp mapped

theorem normalClosure_le_thompsonCenter_of_class_two {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime) (sylow : Sylow prime group)
    (subgroup : Subgroup group)
    (subgroup_le : subgroup ≤ (thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype)
    (closure_le : Subgroup.normalClosure (subgroup : Set group) ≤ sylow)
    (central : commutator ↥(Subgroup.normalClosure (subgroup : Set group)) ≤
      Subgroup.center ↥(Subgroup.normalClosure (subgroup : Set group)))
    (derived_le : ⁅Subgroup.normalClosure (subgroup : Set group), Subgroup.normalClosure (subgroup : Set group)⁆ ≤
      (thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype)
    (stable : primeStable prime (conjugationAction (Subgroup.normalClosure (subgroup : Set group)))) :
    Subgroup.normalClosure (subgroup : Set group) ≤
      (thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype := by
  let closure := Subgroup.normalClosure (subgroup : Set group)
  let inside := closure.subgroupOf (sylow : Subgroup group)
  have : inside.Normal := inferInstance
  have inside_central := subgroupOf_commutator_central closure sylow closure_le central
  have inside_derived := internal_derived_le_of_ambient closure sylow closure_le _ derived_le
  rcases CFSG.OrderReductions.GlaubermanReplacement.glauberman_replacement prime odd_prime sylow.isPGroup'
      inside inside_central inside_derived with all_contain | witness
  · have inside_le : inside ≤ thompsonCenter (sylow : Subgroup group) := by
      rw [thompsonCenter_eq_intersection]
      exact le_sInf all_contain
    have mapped := Subgroup.map_mono (f := (sylow : Subgroup group).subtype) inside_le
    rwa [Subgroup.map_subgroupOf_eq_of_le closure_le] at mapped
  · obtain ⟨maximum, maximal, avoids, normalizes⟩ := witness
    have : IsMulCommutative maximum := maximal.1
    let ambient_maximum := maximum.map (sylow : Subgroup group).subtype
    have : IsMulCommutative ambient_maximum := inferInstance
    have closure_normalizes : closure ≤ Subgroup.normalizer (ambient_maximum : Set group) := by
      have mapped := Subgroup.map_mono (f := (sylow : Subgroup group).subtype) normalizes
      rw [Subgroup.map_subgroupOf_eq_of_le closure_le] at mapped
      exact mapped.trans (Subgroup.le_normalizer_map _)
    let action := conjugationAction closure
    let action_core := actionCore prime action
    have maximum_core := normalized_abelian_le_actionCore prime closure stable ambient_maximum closure_normalizes
    obtain ⟨core_sylow, core_sylow_eq⟩ := exists_sylow_intersection_normal prime action_core sylow
    let smaller := (core_sylow : Subgroup action_core).map action_core.subtype
    change smaller = (sylow : Subgroup group) ⊓ action_core at core_sylow_eq
    have smaller_le : smaller ≤ sylow := by rw [core_sylow_eq]; exact inf_le_left
    have maximum_le_smaller : ambient_maximum ≤ smaller := by
      rw [core_sylow_eq]
      exact le_inf (Subgroup.map_subtype_le maximum) maximum_core
    have maximum_internal : maximum ≤ smaller.subgroupOf (sylow : Subgroup group) :=
      Subgroup.map_le_iff_le_comap.mp maximum_le_smaller
    have center_le := thompsonCenter_le_overgroup_of_contains_maximum
      (smaller.subgroupOf (sylow : Subgroup group)) maximum maximum_internal maximal
    have ambient_center_le := Subgroup.map_mono (f := (sylow : Subgroup group).subtype) center_le
    rw [thompsonCenter_image_subgroupOf smaller sylow smaller_le] at ambient_center_le
    let trap := (thompsonCenter smaller).map smaller.subtype
    have subgroup_trap : subgroup ≤ trap := subgroup_le.trans ambient_center_le
    have frattini := (actionCore_frattini prime action core_sylow).2
    rw [conjugationAction_kernel] at frattini
    have trap_normalizer : Subgroup.normalizer (smaller : Set group) ≤ Subgroup.normalizer (trap : Set group) := by
      intro conjugator conjugator_mem
      exact CFSG.OrderReductions.ThompsonNormalizer.normalizes_thompsonCenter_image smaller conjugator conjugator_mem
    have factorization : Subgroup.centralizer (closure : Set group) ⊔ Subgroup.normalizer (trap : Set group) = ⊤ := by
      apply top_unique
      rw [← frattini]
      exact sup_le_sup_left trap_normalizer _
    have closure_trap := normalClosure_le_of_factorization subgroup trap subgroup_trap factorization
    have maximum_le : ambient_maximum ≤ smaller := maximum_le_smaller
    have internal_maximal := maximum_order_abelian_subgroupOf maximum
      (smaller.subgroupOf (sylow : Subgroup group)) maximum_internal maximal
    have trap_maximum : trap ≤ ambient_maximum := by
      have smaller_center_le := thompsonCenter_le_maximum_order_abelian _ internal_maximal
      have mapped := Subgroup.map_mono (f := (smaller.subgroupOf (sylow : Subgroup group)).subtype) smaller_center_le
      rw [Subgroup.map_subgroupOf_eq_of_le maximum_internal] at mapped
      have mapped_again := Subgroup.map_mono (f := (sylow : Subgroup group).subtype) mapped
      rw [thompsonCenter_image_subgroupOf smaller sylow smaller_le] at mapped_again
      exact mapped_again
    have closure_maximum := closure_trap.trans trap_maximum
    have inside_maximum : inside ≤ maximum := by
      have mapped := closure_maximum
      rw [← Subgroup.map_subgroupOf_eq_of_le closure_le] at mapped
      exact Subgroup.map_subtype_le_map_subtype.mp mapped
    exact False.elim (avoids inside_maximum)

end CFSG.OrderReductions.ThompsonGrowthTrap
