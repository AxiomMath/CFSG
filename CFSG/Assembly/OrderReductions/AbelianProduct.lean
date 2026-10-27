module

public import CFSG.Assembly.OrderReductions.SolvablePrimeCore

public section

namespace CFSG.OrderReductions.AbelianProduct

theorem mutually_normalizing_commutator_le_intersection {group : Type*} [Group group]
    (first second : Subgroup group) [IsMulCommutative first] [IsMulCommutative second]
    (first_normalizes : first ≤ Subgroup.normalizer (second : Set group))
    (second_normalizes : second ≤ Subgroup.normalizer (first : Set group)) :
    ⁅first ⊔ second, first ⊔ second⁆ ≤ first ⊓ second := by
  let product := first ⊔ second
  have : (second.subgroupOf product).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer first_normalizes
  have : (first.subgroupOf product).Normal := by
    change (first.subgroupOf (first ⊔ second)).Normal
    rw [sup_comm]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer second_normalizes
  have internal_sup : first.subgroupOf product ⊔ second.subgroupOf product = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self product
  have commutator_first : commutator product ≤ first.subgroupOf product :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top internal_sup inferInstance
  have commutator_second : commutator product ≤ second.subgroupOf product :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      ((sup_comm (second.subgroupOf product) (first.subgroupOf product)).trans internal_sup) inferInstance
  have mapped_first := Subgroup.map_mono (f := product.subtype) commutator_first
  have mapped_second := Subgroup.map_mono (f := product.subtype) commutator_second
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.subtype_range,
    Subgroup.map_subgroupOf_eq_of_le (show first ≤ product from le_sup_left)] at mapped_first
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.subtype_range,
    Subgroup.map_subgroupOf_eq_of_le (show second ≤ product from le_sup_right)] at mapped_second
  exact le_inf mapped_first mapped_second

theorem intersection_le_product_center {group : Type*} [Group group]
    (first second : Subgroup group) [IsMulCommutative first] [IsMulCommutative second] :
    first ⊓ second ≤ (Subgroup.center ↥(first ⊔ second)).map (first ⊔ second).subtype := by
  intro element element_mem
  have element_product : element ∈ first ⊔ second :=
    (show first ≤ first ⊔ second from le_sup_left) element_mem.1
  have product_centralizes : first ⊔ second ≤ Subgroup.centralizer ({element} : Set group) := by
    apply sup_le
    · intro other other_mem
      apply Subgroup.mem_centralizer_iff.mpr
      intro central central_mem
      have equal_element : central = element := Set.mem_singleton_iff.mp central_mem
      rw [equal_element]
      exact congrArg Subtype.val ((isMulCommutative_iff.mp inferInstance)
        (⟨element, element_mem.1⟩ : first) ⟨other, other_mem⟩)
    · intro other other_mem
      apply Subgroup.mem_centralizer_iff.mpr
      intro central central_mem
      have equal_element : central = element := Set.mem_singleton_iff.mp central_mem
      rw [equal_element]
      exact congrArg Subtype.val ((isMulCommutative_iff.mp inferInstance)
        (⟨element, element_mem.2⟩ : second) ⟨other, other_mem⟩)
  apply Subgroup.mem_map.mpr
  refine ⟨⟨element, element_product⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro other
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (product_centralizes other.property)
    element (Set.mem_singleton element)).symm

theorem mutually_normalizing_commutator_central {group : Type*} [Group group]
    (first second : Subgroup group) [IsMulCommutative first] [IsMulCommutative second]
    (first_normalizes : first ≤ Subgroup.normalizer (second : Set group))
    (second_normalizes : second ≤ Subgroup.normalizer (first : Set group)) :
    commutator ↥(first ⊔ second) ≤ Subgroup.center ↥(first ⊔ second) := by
  have mapped_le := (mutually_normalizing_commutator_le_intersection first second first_normalizes second_normalizes).trans
    (intersection_le_product_center first second)
  have mapped_commutator : (commutator ↥(first ⊔ second)).map (first ⊔ second).subtype =
      ⁅first ⊔ second, first ⊔ second⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.subtype_range]
  rw [← mapped_commutator] at mapped_le
  have preimage_le := Subgroup.comap_mono (f := (first ⊔ second).subtype) mapped_le
  rwa [Subgroup.comap_map_eq_self_of_injective Subtype.val_injective,
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective] at preimage_le

theorem mutually_normalizing_product_nilpotent {group : Type*} [Group group]
    (first second : Subgroup group) [IsMulCommutative first] [IsMulCommutative second]
    (first_normalizes : first ≤ Subgroup.normalizer (second : Set group))
    (second_normalizes : second ≤ Subgroup.normalizer (first : Set group)) :
    Group.IsNilpotent ↥(first ⊔ second) :=
  CFSG.OrderReductions.SolvablePrimeCore.nilpotent_of_commutator_le_center
    (mutually_normalizing_commutator_central first second first_normalizes second_normalizes)

end CFSG.OrderReductions.AbelianProduct
