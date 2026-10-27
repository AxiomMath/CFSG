module

public import CFSG.Assembly.OrderReductions.InvolutionGraph
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OrderReductions.InternalSylow

open CFSG.OrderReductions.InvolutionGraph

theorem sylow_subgroupOf {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (smaller larger : Subgroup group) (contains : smaller ≤ larger)
    (sylow : Sylow prime smaller) :
    ∃ internal : Sylow prime (smaller.subgroupOf larger),
      ((internal : Subgroup (smaller.subgroupOf larger)).map (smaller.subgroupOf larger).subtype).map larger.subtype =
        (sylow : Subgroup smaller).map smaller.subtype := by
  let equivalence := (Subgroup.subgroupOfEquivOfLe contains).symm
  have surjective : Function.Surjective equivalence.toMonoidHom := by
    intro element
    exact ⟨equivalence.symm element, equivalence.apply_symm_apply element⟩
  let internal := sylow.mapSurjective surjective
  refine ⟨internal, ?_⟩
  have internal_eq : (internal : Subgroup (smaller.subgroupOf larger)) =
      (sylow : Subgroup smaller).map equivalence.toMonoidHom := Sylow.coe_mapSurjective surjective sylow
  rw [internal_eq, Subgroup.map_map, Subgroup.map_map]
  have composite : (larger.subtype.comp (smaller.subgroupOf larger).subtype).comp equivalence.toMonoidHom =
      smaller.subtype := by
    ext element
    rfl
  rw [composite]

theorem normalizer_map_subtype_le {group : Type*} [Group group]
    (subgroup : Subgroup group) (internal : Subgroup subgroup) :
    (Subgroup.normalizer (internal : Set subgroup)).map subgroup.subtype ≤
      Subgroup.normalizer (internal.map subgroup.subtype : Set group) := by
  intro element element_mem
  obtain ⟨original, normalizes, equal_image⟩ := Subgroup.mem_map.mp element_mem
  rw [← equal_image]
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have invariant : internal.map (MulAut.conj original).toMonoidHom = internal :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes
  have intertwines : (MulAut.conj original.val).toMonoidHom.comp subgroup.subtype =
      subgroup.subtype.comp (MulAut.conj original).toMonoidHom := by
    ext acting
    rfl
  change (internal.map subgroup.subtype).map (MulAut.conj original.val).toMonoidHom = _
  rw [Subgroup.map_map, intertwines, ← Subgroup.map_map, invariant]

theorem odd_internal_point_normalizer {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (ambient : Subgroup group) (point : Component subgroup)
    (stabilizer_eq : ambient.subgroupOf subgroup = componentStabilizer point)
    (internal : Subgroup subgroup) (image : Subgroup group)
    (image_eq : internal.map subgroup.subtype = image)
    (odd_normalizer : Odd (Nat.card ↥(Subgroup.normalizer (image : Set group) ⊓ ambient))) :
    Odd (Nat.card ↥(Subgroup.normalizer (internal : Set subgroup) ⊓ componentStabilizer point)) := by
  let intersection := Subgroup.normalizer (internal : Set subgroup) ⊓ componentStabilizer point
  have map_le : intersection.map subgroup.subtype ≤ Subgroup.normalizer (image : Set group) ⊓ ambient := by
    apply le_inf
    · rw [← image_eq]
      exact (Subgroup.map_mono (f := subgroup.subtype) (show intersection ≤ Subgroup.normalizer (internal : Set subgroup)
        from inf_le_left)).trans (normalizer_map_subtype_le subgroup internal)
    · have contains := Subgroup.map_mono (f := subgroup.subtype)
        (show intersection ≤ componentStabilizer point from inf_le_right)
      rw [← stabilizer_eq, Subgroup.subgroupOf_map_subtype] at contains
      exact contains.trans inf_le_left
  have odd_image := odd_normalizer.of_dvd_nat (Subgroup.card_dvd_of_le map_le)
  rwa [Subgroup.card_map_of_injective Subtype.val_injective] at odd_image

end CFSG.OrderReductions.InternalSylow
