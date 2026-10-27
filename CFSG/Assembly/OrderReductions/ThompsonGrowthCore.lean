module

public import CFSG.Assembly.OrderReductions.ActionPrimeCore

public section

namespace CFSG.OrderReductions.ThompsonGrowthCore

open CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.PrimeCore CFSG.OrderReductions.CubicConjugation
open CFSG.OrderReductions.ClassTwoCubic

attribute [local instance] commutatorElement

theorem abelian_normalized_quadratic {group : Type*} [Group group]
    (subgroup normal ambient : Subgroup group) [IsMulCommutative subgroup] [normal.Normal]
    (normal_le : normal ≤ ambient)
    (normalizes : ambient ≤ Subgroup.normalizer (subgroup : Set group))
    (actor : subgroup) : quadratic (conjugationAction normal) actor.val := by
  apply (quadratic_conjugation_iff normal actor.val).mpr
  intro element
  have element_normalizes := normalizes (normal_le element.property)
  have conjugate_mem := (Subgroup.mem_normalizer_iff''.mp element_normalizes actor.val⁻¹).mp
    (subgroup.inv_mem actor.property)
  have first_mem : inverseFirstCommutator element.val actor.val ∈ subgroup := by
    change element.val⁻¹ * actor.val⁻¹ * element.val * actor.val ∈ subgroup
    exact subgroup.mul_mem conjugate_mem actor.property
  have commute_first : Commute (inverseFirstCommutator element.val actor.val) actor.val :=
    setLike_mul_comm first_mem actor.property
  change (inverseFirstCommutator element.val actor.val)⁻¹ * actor.val⁻¹ *
    inverseFirstCommutator element.val actor.val * actor.val = 1
  rw [mul_assoc _ actor.val⁻¹ _, ← commute_first.inv_right.eq]
  group

theorem abelian_normalized_le_primeCore {group : Type*} [Group group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group)
    (self_centralizing : Subgroup.centralizer (primeCore prime group : Set group) ≤ primeCore prime group)
    (stable : primeStable prime (conjugationAction (primeCore prime group)))
    (subgroup : Subgroup group) [IsMulCommutative subgroup]
    (normalizes : (sylow : Subgroup group) ≤ Subgroup.normalizer (subgroup : Set group)) :
    subgroup ≤ primeCore prime group := by
  intro actor actor_mem
  have quadratic_actor := abelian_normalized_quadratic subgroup (primeCore prime group) sylow
    (primeCore_le_sylow prime sylow) normalizes ⟨actor, actor_mem⟩
  have actor_core := stable actor quadratic_actor
  rwa [actionCore_primeCore_eq_of_self_centralizing prime self_centralizing] at actor_core

theorem normalClosure_le_primeCore {group : Type*} [Group group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group)
    (self_centralizing : Subgroup.centralizer (primeCore prime group : Set group) ≤ primeCore prime group)
    (stable : primeStable prime (conjugationAction (primeCore prime group)))
    (subgroup : Subgroup group) [IsMulCommutative subgroup]
    (normalizes : (sylow : Subgroup group) ≤ Subgroup.normalizer (subgroup : Set group)) :
    Subgroup.normalClosure (subgroup : Set group) ≤ primeCore prime group :=
  Subgroup.normalClosure_le_normal
    (abelian_normalized_le_primeCore prime sylow self_centralizing stable subgroup normalizes)

theorem normalClosure_commutator_le {group : Type*} [Group group]
    (subgroup normal kernel : Subgroup group) [normal.Normal] [kernel.Normal]
    (commutator_le : ⁅subgroup, normal⁆ ≤ kernel) :
    ⁅Subgroup.normalClosure (subgroup : Set group), normal⁆ ≤ kernel := by
  let projection := QuotientGroup.mk' kernel
  have map_commutator_bot : ⁅subgroup.map projection, normal.map projection⁆ = ⊥ := by
    rw [← Subgroup.map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rwa [QuotientGroup.ker_mk']
  have image_centralizes := Subgroup.commutator_eq_bot_iff_le_centralizer.mp map_commutator_bot
  have subgroup_le : subgroup ≤ (Subgroup.centralizer (normal.map projection : Set (group ⧸ kernel))).comap projection :=
    Subgroup.map_le_iff_le_comap.mp image_centralizes
  have closure_le := Subgroup.normalClosure_le_normal subgroup_le
  have image_closure_le := Subgroup.map_le_iff_le_comap.mpr closure_le
  have image_bot := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr image_closure_le
  rw [← Subgroup.map_commutator] at image_bot
  have kernel_le := (Subgroup.map_eq_bot_iff _).mp image_bot
  rwa [QuotientGroup.ker_mk'] at kernel_le

theorem normalClosure_centralizes_kernel {group : Type*} [Group group]
    (subgroup kernel : Subgroup group) [IsMulCommutative subgroup] [kernel.Normal]
    (contains : kernel ≤ subgroup) :
    Subgroup.normalClosure (subgroup : Set group) ≤ Subgroup.centralizer (kernel : Set group) := by
  apply Subgroup.normalClosure_le_normal
  intro element element_mem
  apply Subgroup.mem_centralizer_iff.mpr
  intro value value_mem
  exact setLike_mul_comm (contains value_mem) element_mem

theorem normalClosure_class_two {group : Type*} [Group group]
    (subgroup normal kernel : Subgroup group) [IsMulCommutative subgroup] [normal.Normal] [kernel.Normal]
    (contains : kernel ≤ subgroup) (closure_le : Subgroup.normalClosure (subgroup : Set group) ≤ normal)
    (commutator_le : ⁅subgroup, normal⁆ ≤ kernel) :
    ⁅Subgroup.normalClosure (subgroup : Set group), Subgroup.normalClosure (subgroup : Set group)⁆ ≤ kernel ∧
      commutator ↥(Subgroup.normalClosure (subgroup : Set group)) ≤
        Subgroup.center ↥(Subgroup.normalClosure (subgroup : Set group)) := by
  let closure := Subgroup.normalClosure (subgroup : Set group)
  have derived_le : ⁅closure, closure⁆ ≤ kernel :=
    (Subgroup.commutator_mono le_rfl closure_le).trans (normalClosure_commutator_le subgroup normal kernel commutator_le)
  refine ⟨derived_le, ?_⟩
  have centralizes := normalClosure_centralizes_kernel subgroup kernel contains
  intro element element_mem
  apply Subgroup.mem_center_iff.mpr
  intro other
  apply Subtype.ext
  have image_mem : element.val ∈ ⁅closure, closure⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.mem_map.mpr ⟨element, element_mem, rfl⟩
  exact (Subgroup.mem_centralizer_iff.mp (centralizes other.property) element.val (derived_le image_mem)).symm

end CFSG.OrderReductions.ThompsonGrowthCore
