module

public import CFSG.Assembly.OrderReductions.ThompsonFixedGrowth
public import CFSG.Assembly.OrderReductions.ThompsonGrowthTrap

public section

namespace CFSG.OrderReductions.ThompsonNormality

open CFSG.OrderReductions.ThompsonCenter CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.PrimeCore
open CFSG.OrderReductions.ThompsonFixedGrowth CFSG.OrderReductions.ThompsonGrowthCore CFSG.OrderReductions.ThompsonGrowthTrap

theorem normal_growth_inside_thompsonCenter {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime) (sylow : Sylow prime group)
    (self_centralizing : Subgroup.centralizer (primeCore prime group : Set group) ≤ primeCore prime group)
    (stable : ∀ normal : Subgroup group, ∀ [normal.Normal], IsPGroup prime normal →
      primeStable prime (conjugationAction normal))
    (kernel : Subgroup group) [kernel.Normal]
    (proper : kernel < (thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype) :
    ∃ larger : Subgroup group, larger.Normal ∧ kernel < larger ∧
      larger ≤ (thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype := by
  let sylow_group := (sylow : Subgroup group)
  let center := thompsonCenter sylow_group
  let center_image := center.map sylow_group.subtype
  have kernel_le_sylow : kernel ≤ sylow_group := proper.le.trans (Subgroup.map_subtype_le center)
  let kernel_internal := kernel.subgroupOf sylow_group
  have kernel_internal_lt : kernel_internal < center := by
    apply Subgroup.map_subtype_lt_map_subtype.mp
    rw [Subgroup.map_subgroupOf_eq_of_le kernel_le_sylow]
    exact proper
  let fixed := fixedPreimage center kernel_internal
  have fixed_properties := thompson_fixed_growth prime sylow.isPGroup' kernel_internal kernel_internal_lt
  let image := fixed.map sylow_group.subtype
  have kernel_lt_image : kernel < image := by
    rw [← Subgroup.map_subgroupOf_eq_of_le kernel_le_sylow]
    exact Subgroup.map_subtype_lt_map_subtype.mpr fixed_properties.1
  have image_le_center : image ≤ center_image := Subgroup.map_mono fixed_properties.2.1
  have : IsMulCommutative fixed := fixed_properties.2.2.1
  have : IsMulCommutative image := inferInstance
  have sylow_normalizes : sylow_group ≤ Subgroup.normalizer (image : Set group) := by
    have : fixed.Normal := inferInstance
    intro actor actor_mem
    have internal_mem : (⟨actor, actor_mem⟩ : sylow_group) ∈ Subgroup.normalizer (fixed : Set sylow_group) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    exact Subgroup.le_normalizer_map sylow_group.subtype (Subgroup.mem_map.mpr
      ⟨⟨actor, actor_mem⟩, internal_mem, rfl⟩)
  have image_commutator_le : ⁅image, sylow_group⁆ ≤ kernel := by
    have mapped := Subgroup.map_mono (f := sylow_group.subtype) fixed_properties.2.2.2
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.subtype_range,
      Subgroup.map_subgroupOf_eq_of_le kernel_le_sylow] at mapped
    exact mapped
  let closure := Subgroup.normalClosure (image : Set group)
  have closure_core : closure ≤ primeCore prime group := normalClosure_le_primeCore prime sylow
    self_centralizing (stable _ (primeCore_isPGroup prime group)) image sylow_normalizes
  have closure_sylow : closure ≤ sylow_group := closure_core.trans (primeCore_le_sylow prime sylow)
  have image_core_commutator : ⁅image, primeCore prime group⁆ ≤ kernel :=
    (Subgroup.commutator_mono le_rfl (primeCore_le_sylow prime sylow)).trans image_commutator_le
  have closure_properties := normalClosure_class_two image (primeCore prime group) kernel kernel_lt_image.le
    closure_core image_core_commutator
  have derived_le_center : ⁅closure, closure⁆ ≤ center_image := closure_properties.1.trans proper.le
  have closure_prime : IsPGroup prime closure := (primeCore_isPGroup prime group).to_le closure_core
  have closure_center := normalClosure_le_thompsonCenter_of_class_two prime odd_prime sylow image image_le_center
    closure_sylow closure_properties.2 derived_le_center (stable closure closure_prime)
  exact ⟨closure, inferInstance, lt_of_lt_of_le kernel_lt_image Subgroup.le_normalClosure, closure_center⟩

theorem thompsonCenter_image_normal {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime) (sylow : Sylow prime group)
    (self_centralizing : Subgroup.centralizer (primeCore prime group : Set group) ≤ primeCore prime group)
    (stable : ∀ normal : Subgroup group, ∀ [normal.Normal], IsPGroup prime normal →
      primeStable prime (conjugationAction normal)) :
    ((thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype).Normal := by
  classical
  let center := (thompsonCenter (sylow : Subgroup group)).map (sylow : Subgroup group).subtype
  let candidates : Set (Subgroup group) := {subgroup | subgroup.Normal ∧ subgroup ≤ center}
  have nonempty : candidates.Nonempty := ⟨⊥, inferInstance, bot_le⟩
  obtain ⟨kernel, maximal⟩ := Set.Finite.exists_maximalFor (fun subgroup : Subgroup group => subgroup)
    candidates (Set.toFinite _) nonempty
  have : kernel.Normal := maximal.prop.1
  change center.Normal
  by_cases equal : kernel = center
  · rw [← equal]
    infer_instance
  · have proper : kernel < center := lt_of_le_of_ne maximal.prop.2 equal
    obtain ⟨larger, normal, grows, contains⟩ := normal_growth_inside_thompsonCenter
      prime odd_prime sylow self_centralizing stable kernel proper
    exact False.elim (maximal.not_gt ⟨normal, contains⟩ grows)

end CFSG.OrderReductions.ThompsonNormality
