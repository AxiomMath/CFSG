module

public import CFSG.Assembly.OrderReductions.ReplacementGeometry

public section

namespace CFSG.OrderReductions.ReplacementGrowth

open CFSG.OrderReductions.ReplacementGeometry CFSG.OrderReductions.CubicConjugation
open scoped Pointwise

@[expose] def localNormalizer {group : Type*} [Group group] (normal subgroup : Subgroup group) : Subgroup group :=
  normal ⊓ Subgroup.normalizer (subgroup : Set group)

@[expose] def normalizerProduct {group : Type*} [Group group] (normal subgroup : Subgroup group) : Subgroup group :=
  subgroup ⊔ localNormalizer normal subgroup

theorem normalizerProduct_normalizes {group : Type*} [Group group] (normal subgroup : Subgroup group) :
    normalizerProduct normal subgroup ≤ Subgroup.normalizer (subgroup : Set group) :=
  sup_le Subgroup.le_normalizer inf_le_right

theorem normalizerProduct_le_product {group : Type*} [Group group] (normal subgroup : Subgroup group) :
    normalizerProduct normal subgroup ≤ subgroup ⊔ normal :=
  sup_le le_sup_left (inf_le_left.trans le_sup_right)

theorem normalizerProduct_ne_product {group : Type*} [Group group] (normal subgroup : Subgroup group)
    (not_normalizes : ¬ normal ≤ Subgroup.normalizer (subgroup : Set group)) :
    normalizerProduct normal subgroup ≠ subgroup ⊔ normal := by
  intro equal
  apply not_normalizes
  exact (show normal ≤ subgroup ⊔ normal from le_sup_right).trans
    (equal ▸ normalizerProduct_normalizes normal subgroup)

theorem exists_normalizing_element_outside {group : Type*} [Group group]
    (normal subgroup : Subgroup group) [normal.Normal]
    (condition : NormalizerCondition ↥(subgroup ⊔ normal))
    (not_normalizes : ¬ normal ≤ Subgroup.normalizer (subgroup : Set group)) :
    ∃ element : normal, element.val ∉ normalizerProduct normal subgroup ∧
      element.val ∈ Subgroup.normalizer (normalizerProduct normal subgroup : Set group) := by
  let ambient := subgroup ⊔ normal
  let small := normalizerProduct normal subgroup
  have contains : small ≤ ambient := normalizerProduct_le_product normal subgroup
  have proper : small.subgroupOf ambient ≠ ⊤ := by
    intro equal
    have mapped := congrArg (Subgroup.map ambient.subtype) equal
    rw [Subgroup.map_subgroupOf_eq_of_le contains, ← MonoidHom.range_eq_map, Subgroup.subtype_range] at mapped
    exact normalizerProduct_ne_product normal subgroup not_normalizes mapped
  have internal_lt := condition (small.subgroupOf ambient) (lt_top_iff_ne_top.mpr proper)
  obtain ⟨value, value_mem, value_outside⟩ := IsConcreteLE.exists_of_lt internal_lt
  have ambient_normalizes : value.val ∈ Subgroup.normalizer (small : Set group) := by
    rw [← Subgroup.subgroupOf_normalizer_eq contains] at value_mem
    exact value_mem
  obtain ⟨first, first_mem, second, second_mem, equal⟩ :=
    Subgroup.mem_sup_of_normal_right.mp value.property
  have first_small : first ∈ small := (show subgroup ≤ small from le_sup_left) first_mem
  have first_normalizes : first ∈ Subgroup.normalizer (small : Set group) := Subgroup.le_normalizer first_small
  have second_eq : first⁻¹ * value.val = second := by rw [← equal]; group
  have second_normalizes := (Subgroup.normalizer (small : Set group)).mul_mem
    ((Subgroup.normalizer (small : Set group)).inv_mem first_normalizes) ambient_normalizes
  rw [second_eq] at second_normalizes
  refine ⟨⟨second, second_mem⟩, ?_, second_normalizes⟩
  intro second_small
  apply value_outside
  change value.val ∈ small
  rw [← equal]
  exact small.mul_mem first_small second_small

theorem ambient_normalizes_replacement {group : Type*} [Group group]
    (subgroup normal ambient : Subgroup group) [normal.Normal]
    (contains : subgroup ≤ ambient)
    (ambient_normalizes : ambient ≤ Subgroup.normalizer (subgroup : Set group))
    (derived_le : ⁅normal, normal⁆ ≤ subgroup) (element : normal)
    (normalizes : element.val ∈ Subgroup.normalizer (ambient : Set group)) :
    ambient ≤ Subgroup.normalizer (replacement subgroup element.val : Set group) := by
  have pair := conjugate_pair_mutually_normalizes subgroup ambient contains ambient_normalizes normalizes
  rw [replacement_eq_intersection_sup_normal subgroup normal element
    (intersection_le_conjugate_intersection subgroup normal derived_le element.property) pair.2]
  apply le_trans _ (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  apply le_inf
  · exact (le_inf ambient_normalizes
      (normalizes_conjugate subgroup ambient ambient_normalizes normalizes)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  · apply le_trans _ Subgroup.inf_normalizer_le_normalizer_inf
    apply le_inf
    · exact (le_inf ambient_normalizes
        (normalizes_conjugate subgroup ambient ambient_normalizes normalizes)).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    · exact Subgroup.le_normalizer_of_normal

theorem conjugator_normalizes_replacement {group : Type*} [Group group] [Finite group]
    (subgroup normal : Subgroup group) [normal.Normal] (derived_le : ⁅normal, normal⁆ ≤ subgroup)
    (element : normal) :
    element.val ∈ Subgroup.normalizer (replacement subgroup element.val : Set group) := by
  let replaced := replacement subgroup element.val
  let intersection := subgroup ⊓ conjugate subgroup element.val
  let commutators := firstCommutators subgroup element.val
  have derived_intersection : ⁅normal, normal⁆ ≤ intersection := by
    apply le_trans _ (intersection_le_conjugate_intersection subgroup normal derived_le element.property)
    exact le_inf derived_le (Subgroup.commutator_le_self normal)
  have right_conjugate_mem : ∀ value ∈ replaced, element.val⁻¹ * value * element.val ∈ replaced := by
    have intersection_le : intersection ≤ replaced.comap (MulAut.conj element.val⁻¹).toMonoidHom := by
      intro value value_mem
      change (MulAut.conj element.val⁻¹) value ∈ replaced
      have commutator_mem : inverseFirstCommutator value element.val ∈ replaced :=
        (show commutators ≤ replaced from le_sup_right)
          (Subgroup.subset_closure (Set.mem_range_self (⟨value, value_mem.1⟩ : subgroup)))
      have value_replaced := (show intersection ≤ replaced from le_sup_left) value_mem
      have product_mem := replaced.mul_mem value_replaced commutator_mem
      have conjugate_eq : value * inverseFirstCommutator value element.val =
          (MulAut.conj element.val⁻¹) value := by
        rw [MulAut.conj_apply, inv_inv]
        dsimp [inverseFirstCommutator]
        group
      rwa [conjugate_eq] at product_mem
    have commutators_le : commutators ≤ replaced.comap (MulAut.conj element.val⁻¹).toMonoidHom := by
      intro value value_mem
      have normal_mem := firstCommutators_le_normal subgroup normal element.property value_mem
      have commutator_mem : inverseFirstCommutator value element.val ∈ replaced :=
        (show intersection ≤ replaced from le_sup_left)
          (derived_intersection (inverseFirstCommutator_mem normal normal_mem element.property))
      have value_replaced := (show commutators ≤ replaced from le_sup_right) value_mem
      change (MulAut.conj element.val⁻¹) value ∈ replaced
      have product_mem := replaced.mul_mem value_replaced commutator_mem
      have conjugate_eq : value * inverseFirstCommutator value element.val =
          (MulAut.conj element.val⁻¹) value := by
        rw [MulAut.conj_apply, inv_inv]
        dsimp [inverseFirstCommutator]
        group
      rwa [conjugate_eq] at product_mem
    intro value value_mem
    have mapped := (sup_le intersection_le commutators_le) value_mem
    change (MulAut.conj element.val⁻¹) value ∈ replaced at mapped
    simpa only [MulAut.conj_apply, inv_inv] using mapped
  have inverse_normalizes : element.val⁻¹ ∈ Subgroup.normalizer (replaced : Set group) := by
    apply Subgroup.mem_normalizer_fintype
    intro value value_mem
    change element.val⁻¹ * value * (element.val⁻¹)⁻¹ ∈ replaced
    simpa only [inv_inv] using right_conjugate_mem value value_mem
  simpa only [inv_inv] using (Subgroup.normalizer (replaced : Set group)).inv_mem inverse_normalizes

theorem replacement_grows_normalizer {group : Type*} [Group group] [Finite group]
    (subgroup normal : Subgroup group) [normal.Normal]
    (derived_le : ⁅normal, normal⁆ ≤ subgroup) (element : normal)
    (outside : element.val ∉ normalizerProduct normal subgroup)
    (normalizes : element.val ∈ Subgroup.normalizer (normalizerProduct normal subgroup : Set group)) :
    localNormalizer normal subgroup < localNormalizer normal (replacement subgroup element.val) := by
  have contains : subgroup ≤ normalizerProduct normal subgroup := le_sup_left
  have normalizer_le := ambient_normalizes_replacement subgroup normal (normalizerProduct normal subgroup)
    contains (normalizerProduct_normalizes normal subgroup) derived_le element normalizes
  apply lt_of_le_of_ne
  · exact le_inf inf_le_left ((show localNormalizer normal subgroup ≤ normalizerProduct normal subgroup from le_sup_right).trans normalizer_le)
  · intro equal
    have element_new : element.val ∈ localNormalizer normal (replacement subgroup element.val) :=
      ⟨element.property, conjugator_normalizes_replacement subgroup normal derived_le element⟩
    rw [← equal] at element_new
    exact outside ((show localNormalizer normal subgroup ≤ normalizerProduct normal subgroup from le_sup_right) element_new)

end CFSG.OrderReductions.ReplacementGrowth
