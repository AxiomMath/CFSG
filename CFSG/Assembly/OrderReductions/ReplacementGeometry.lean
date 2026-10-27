module

public import CFSG.Assembly.OrderReductions.ThompsonCenter
public import CFSG.Assembly.OrderReductions.AbelianProduct
public import CFSG.Assembly.OrderReductions.CubicConjugation

public section

namespace CFSG.OrderReductions.ReplacementGeometry

open CFSG.OrderReductions.CubicConjugation
open scoped Pointwise

attribute [local instance] commutatorElement

@[expose] def conjugate {group : Type*} [Group group] (subgroup : Subgroup group) (element : group) : Subgroup group :=
  subgroup.map (MulAut.conj element⁻¹).toMonoidHom

@[expose] def firstCommutators {group : Type*} [Group group] (subgroup : Subgroup group) (element : group) : Subgroup group :=
  Subgroup.closure (Set.range fun member : subgroup => inverseFirstCommutator member.val element)

@[expose] def replacement {group : Type*} [Group group] (subgroup : Subgroup group) (element : group) : Subgroup group :=
  (subgroup ⊓ conjugate subgroup element) ⊔ firstCommutators subgroup element

theorem inverseFirstCommutator_mem {group : Type*} [Group group]
    (subgroup : Subgroup group) {first second : group} (first_mem : first ∈ subgroup) (second_mem : second ∈ subgroup) :
    inverseFirstCommutator first second ∈ ⁅subgroup, subgroup⁆ := by
  simpa only [commutatorElement_def, inv_inv, inverseFirstCommutator] using
    Subgroup.commutator_mem_commutator (subgroup.inv_mem first_mem) (subgroup.inv_mem second_mem)

theorem conjugate_mem {group : Type*} [Group group] (subgroup : Subgroup group)
    (conjugator : group) (element : subgroup) :
    conjugator⁻¹ * element.val * conjugator ∈ conjugate subgroup conjugator := by
  apply Subgroup.mem_map.mpr
  refine ⟨element.val, element.property, ?_⟩
  change (MulAut.conj conjugator⁻¹) element.val = _
  rw [MulAut.conj_apply, inv_inv]

theorem conjugate_le_of_normalizes {group : Type*} [Group group]
    (subgroup ambient : Subgroup group) (contains : subgroup ≤ ambient)
    {element : group} (normalizes : element ∈ Subgroup.normalizer (ambient : Set group)) :
    conjugate subgroup element ≤ ambient := by
  have invariant := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer (ambient : Set group)).inv_mem normalizes)
  exact (Subgroup.map_mono contains).trans invariant.le

theorem normalizes_conjugate {group : Type*} [Group group]
    (subgroup ambient : Subgroup group)
    (ambient_normalizes : ambient ≤ Subgroup.normalizer (subgroup : Set group))
    {element : group} (normalizes : element ∈ Subgroup.normalizer (ambient : Set group)) :
    ambient ≤ Subgroup.normalizer (conjugate subgroup element : Set group) := by
  have invariant := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer (ambient : Set group)).inv_mem normalizes)
  change ambient.map (MulAut.conj element⁻¹).toMonoidHom = ambient at invariant
  have mapped := Subgroup.map_mono (f := (MulAut.conj element⁻¹).toMonoidHom) ambient_normalizes
  rw [invariant, Subgroup.map_equiv_normalizer_eq] at mapped
  exact mapped

theorem conjugate_pair_mutually_normalizes {group : Type*} [Group group]
    (subgroup ambient : Subgroup group) (contains : subgroup ≤ ambient)
    (ambient_normalizes : ambient ≤ Subgroup.normalizer (subgroup : Set group))
    {element : group} (normalizes : element ∈ Subgroup.normalizer (ambient : Set group)) :
    subgroup ≤ Subgroup.normalizer (conjugate subgroup element : Set group) ∧
      conjugate subgroup element ≤ Subgroup.normalizer (subgroup : Set group) :=
  ⟨contains.trans (normalizes_conjugate subgroup ambient ambient_normalizes normalizes),
    (conjugate_le_of_normalizes subgroup ambient contains normalizes).trans ambient_normalizes⟩

theorem firstCommutators_le_product {group : Type*} [Group group] (subgroup : Subgroup group) (element : group) :
    firstCommutators subgroup element ≤ subgroup ⊔ conjugate subgroup element := by
  apply (Subgroup.closure_le _).mpr
  rintro value ⟨member, rfl⟩
  have first_mem : member.val⁻¹ ∈ subgroup ⊔ conjugate subgroup element :=
    (show subgroup ≤ subgroup ⊔ conjugate subgroup element from le_sup_left) (subgroup.inv_mem member.property)
  have second_mem : element⁻¹ * member.val * element ∈ subgroup ⊔ conjugate subgroup element :=
    (show conjugate subgroup element ≤ subgroup ⊔ conjugate subgroup element from le_sup_right)
      (conjugate_mem subgroup element member)
  change inverseFirstCommutator member.val element ∈ subgroup ⊔ conjugate subgroup element
  simpa only [inverseFirstCommutator, mul_assoc] using
    (subgroup ⊔ conjugate subgroup element).mul_mem first_mem second_mem

theorem firstCommutators_le_normal {group : Type*} [Group group]
    (subgroup normal : Subgroup group) [normal.Normal] {element : group} (element_mem : element ∈ normal) :
    firstCommutators subgroup element ≤ normal := by
  apply (Subgroup.closure_le _).mpr
  rintro value ⟨member, rfl⟩
  have conjugate_mem := Subgroup.Normal.conj_mem' inferInstance element⁻¹ (normal.inv_mem element_mem) member.val
  change inverseFirstCommutator member.val element ∈ normal
  simpa only [inverseFirstCommutator, mul_assoc] using normal.mul_mem conjugate_mem element_mem

theorem intersection_normal_in_normal {group : Type*} [Group group]
    (subgroup normal : Subgroup group) (derived_le : ⁅normal, normal⁆ ≤ subgroup) :
    normal ≤ Subgroup.normalizer ((subgroup ⊓ normal : Subgroup group) : Set group) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator conjugator_mem element element_mem
  have commutator_mem := Subgroup.commutator_mem_commutator conjugator_mem element_mem.2
  have conjugate_eq : conjugator * element * conjugator⁻¹ = ⁅conjugator, element⁆ * element := by
    rw [commutatorElement_def]
    group
  rw [conjugate_eq]
  exact ⟨subgroup.mul_mem (derived_le commutator_mem) element_mem.1,
    normal.mul_mem (Subgroup.commutator_le_self normal commutator_mem) element_mem.2⟩

theorem intersection_le_conjugate_intersection {group : Type*} [Group group]
    (subgroup normal : Subgroup group) (derived_le : ⁅normal, normal⁆ ≤ subgroup)
    {element : group} (element_mem : element ∈ normal) :
    subgroup ⊓ normal ≤ subgroup ⊓ conjugate subgroup element := by
  have normalizes := intersection_normal_in_normal subgroup normal derived_le element_mem
  intro value value_mem
  refine ⟨value_mem.1, ?_⟩
  have conjugated_mem := (Subgroup.mem_normalizer_iff.mp normalizes value).mp value_mem
  apply Subgroup.mem_map.mpr
  refine ⟨element * value * element⁻¹, conjugated_mem.1, ?_⟩
  change (MulAut.conj element⁻¹) (element * value * element⁻¹) = value
  rw [MulAut.conj_apply, inv_inv]
  group

theorem cubic_trivial_of_conjugate_pair {group : Type*} [Group group]
    (subgroup : Subgroup group) [IsMulCommutative subgroup] (element : group)
    (first_normalizes : subgroup ≤ Subgroup.normalizer (conjugate subgroup element : Set group))
    (second_normalizes : conjugate subgroup element ≤ Subgroup.normalizer (subgroup : Set group)) :
    ∀ first second third : subgroup,
      inverseFirstCommutator
        (inverseFirstCommutator (inverseFirstCommutator element first.val) second.val) third.val = 1 := by
  have : IsMulCommutative (conjugate subgroup element) := by
    change IsMulCommutative (subgroup.map (MulAut.conj element⁻¹).toMonoidHom)
    infer_instance
  let product := subgroup ⊔ conjugate subgroup element
  have derived_le := CFSG.OrderReductions.AbelianProduct.mutually_normalizing_commutator_le_intersection
    subgroup (conjugate subgroup element) first_normalizes second_normalizes
  intro first second third
  have first_mem : inverseFirstCommutator element first.val ∈ product := by
    rw [inverseFirstCommutator_swap]
    exact product.inv_mem (firstCommutators_le_product subgroup element
      (Subgroup.subset_closure (Set.mem_range_self first)))
  have second_mem := inverseFirstCommutator_mem product first_mem
    (show second.val ∈ product from (show subgroup ≤ product from le_sup_left) second.property)
  have second_subgroup := (derived_le second_mem).1
  have equal := setLike_mul_comm (s := subgroup) second_subgroup third.property
  let intermediate := inverseFirstCommutator (inverseFirstCommutator element first.val) second.val
  change intermediate⁻¹ * third.val⁻¹ * intermediate * third.val = 1
  have commute_intermediate : Commute intermediate third.val := equal
  rw [mul_assoc intermediate⁻¹ third.val⁻¹ intermediate]
  rw [← commute_intermediate.inv_right.eq]
  group

theorem firstCommutators_abelian {group : Type*} [Group group]
    (subgroup normal : Subgroup group) [IsMulCommutative subgroup] [normal.Normal]
    (central : commutator normal ≤ Subgroup.center normal) (odd_order : Odd (Nat.card normal))
    (derived_le : ⁅normal, normal⁆ ≤ subgroup) (element : normal)
    (first_normalizes : subgroup ≤ Subgroup.normalizer (conjugate subgroup element.val : Set group))
    (second_normalizes : conjugate subgroup element.val ≤ Subgroup.normalizer (subgroup : Set group)) :
    IsMulCommutative ↥(firstCommutators subgroup element.val) := by
  have centralizes : subgroup ≤ Subgroup.centralizer ((⁅normal, normal⁆ : Subgroup group) : Set group) := by
    intro actor actor_mem
    apply Subgroup.mem_centralizer_iff.mpr
    intro value value_mem
    exact setLike_mul_comm (s := subgroup) (derived_le value_mem) actor_mem
  have reverse_abelian := cubic_trivial_conjugation_abelian subgroup normal central odd_order centralizes
    element (cubic_trivial_of_conjugate_pair subgroup element.val first_normalizes second_normalizes)
  apply CFSG.subgroup_isMulCommutative_closure
  rintro left ⟨first, rfl⟩ right ⟨second, rfl⟩
  have commutes := setLike_mul_comm
    (s := Subgroup.closure (Set.range fun actor : subgroup => inverseFirstCommutator element.val actor.val))
    (Subgroup.subset_closure (Set.mem_range_self first))
    (Subgroup.subset_closure (Set.mem_range_self second))
  have commute_reverse : Commute (inverseFirstCommutator element.val first.val)
      (inverseFirstCommutator element.val second.val) := commutes
  have commute_inverse := commute_reverse.inv_inv
  change inverseFirstCommutator first.val element.val * inverseFirstCommutator second.val element.val =
    inverseFirstCommutator second.val element.val * inverseFirstCommutator first.val element.val
  rw [inverseFirstCommutator_swap element.val first.val,
    inverseFirstCommutator_swap element.val second.val]
  exact commute_inverse.eq

theorem commuting_sup_abelian {group : Type*} [Group group]
    (first second : Subgroup group) [IsMulCommutative first] [IsMulCommutative second]
    (commutes : first ≤ Subgroup.centralizer (second : Set group)) :
    IsMulCommutative ↥(first ⊔ second) := by
  rw [Subgroup.sup_eq_closure]
  apply CFSG.subgroup_isMulCommutative_closure
  intro left left_mem right right_mem
  rcases left_mem with left_first | left_second <;> rcases right_mem with right_first | right_second
  · exact setLike_mul_comm left_first right_first
  · exact (Subgroup.mem_centralizer_iff.mp (commutes left_first) right right_second).symm
  · exact Subgroup.mem_centralizer_iff.mp (commutes right_first) left left_second
  · exact setLike_mul_comm left_second right_second

theorem replacement_abelian {group : Type*} [Group group]
    (subgroup normal : Subgroup group) [IsMulCommutative subgroup] [normal.Normal]
    (central : commutator normal ≤ Subgroup.center normal) (odd_order : Odd (Nat.card normal))
    (derived_le : ⁅normal, normal⁆ ≤ subgroup) (element : normal)
    (first_normalizes : subgroup ≤ Subgroup.normalizer (conjugate subgroup element.val : Set group))
    (second_normalizes : conjugate subgroup element.val ≤ Subgroup.normalizer (subgroup : Set group)) :
    IsMulCommutative ↥(replacement subgroup element.val) := by
  let intersection := subgroup ⊓ conjugate subgroup element.val
  have : IsMulCommutative intersection := IsMulCommutative.of_setLike_mul_comm
    (fun _ first_mem _ second_mem => setLike_mul_comm (s := subgroup) first_mem.1 second_mem.1)
  have : IsMulCommutative (conjugate subgroup element.val) := by
    change IsMulCommutative (subgroup.map (MulAut.conj element.val⁻¹).toMonoidHom)
    infer_instance
  have : IsMulCommutative (firstCommutators subgroup element.val) :=
    firstCommutators_abelian subgroup normal central odd_order derived_le element first_normalizes second_normalizes
  have center_le := CFSG.OrderReductions.AbelianProduct.intersection_le_product_center subgroup (conjugate subgroup element.val)
  apply commuting_sup_abelian intersection (firstCommutators subgroup element.val)
  intro value value_mem
  obtain ⟨internal, internal_center, image_eq⟩ := Subgroup.mem_map.mp (center_le value_mem)
  apply Subgroup.mem_centralizer_iff.mpr
  intro other other_mem
  have product_mem := firstCommutators_le_product subgroup element.val other_mem
  have equal := Subgroup.mem_center_iff.mp internal_center ⟨other, product_mem⟩
  have ambient_equal := congrArg Subtype.val equal
  change other * internal.val = internal.val * other at ambient_equal
  change internal.val = value at image_eq
  rwa [image_eq] at ambient_equal

theorem product_eq_subgroup_sup_firstCommutators {group : Type*} [Group group]
    (subgroup : Subgroup group) (element : group) :
    subgroup ⊔ conjugate subgroup element = subgroup ⊔ firstCommutators subgroup element := by
  apply le_antisymm
  · apply sup_le le_sup_left
    rintro value ⟨original, original_mem, image_eq⟩
    have commutator_mem : inverseFirstCommutator original element ∈ subgroup ⊔ firstCommutators subgroup element :=
      (show firstCommutators subgroup element ≤ subgroup ⊔ firstCommutators subgroup element from le_sup_right)
        (Subgroup.subset_closure (Set.mem_range_self (⟨original, original_mem⟩ : subgroup)))
    have product_mem := (subgroup ⊔ firstCommutators subgroup element).mul_mem
      ((show subgroup ≤ subgroup ⊔ firstCommutators subgroup element from le_sup_left) original_mem) commutator_mem
    have value_eq : original * inverseFirstCommutator original element = value := by
      rw [← image_eq]
      change original * (original⁻¹ * element⁻¹ * original * element) =
        (MulAut.conj element⁻¹) original
      rw [MulAut.conj_apply, inv_inv]
      group
    rwa [value_eq] at product_mem
  · exact sup_le le_sup_left (firstCommutators_le_product subgroup element)

theorem card_subgroupOf_eq_intersection {group : Type*} [Group group]
    (first second : Subgroup group) :
    Nat.card (second.subgroupOf first) = Nat.card ↥(first ⊓ second) := by
  rw [← Subgroup.inf_subgroupOf_left second first]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem card_product_mul_card_intersection {group : Type*} [Group group]
    (first second : Subgroup group)
    (normalizes : first ≤ Subgroup.normalizer (second : Set group)) :
    Nat.card ↥(first ⊔ second) * Nat.card ↥(first ⊓ second) = Nat.card first * Nat.card second := by
  have : (second.subgroupOf first).Normal := Subgroup.normal_subgroupOf_of_le_normalizer normalizes
  have : (second.subgroupOf (first ⊔ second)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer normalizes
  have quotient_card := Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient first second normalizes).toEquiv
  have first_card := (second.subgroupOf first).card_mul_index
  have product_card := (second.subgroupOf (first ⊔ second)).card_mul_index
  rw [Subgroup.index_eq_card, card_subgroupOf_eq_intersection] at first_card
  rw [Subgroup.index_eq_card,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show second ≤ first ⊔ second from le_sup_right)).toEquiv,
    ← quotient_card] at product_card
  rw [← product_card]
  calc
    Nat.card second * Nat.card (first ⧸ second.subgroupOf first) * Nat.card ↥(first ⊓ second) =
        Nat.card second * (Nat.card ↥(first ⊓ second) * Nat.card (first ⧸ second.subgroupOf first)) := by ac_rfl
    _ = Nat.card second * Nat.card first := by rw [first_card]
    _ = Nat.card first * Nat.card second := mul_comm _ _

theorem replacement_le_product {group : Type*} [Group group] (subgroup : Subgroup group) (element : group) :
    replacement subgroup element ≤ subgroup ⊔ conjugate subgroup element :=
  sup_le (inf_le_left.trans le_sup_left) (firstCommutators_le_product subgroup element)

theorem product_normalizes_subgroup {group : Type*} [Group group]
    (subgroup : Subgroup group) (element : group)
    (normalizes : conjugate subgroup element ≤ Subgroup.normalizer (subgroup : Set group)) :
    subgroup ⊔ conjugate subgroup element ≤ Subgroup.normalizer (subgroup : Set group) :=
  sup_le Subgroup.le_normalizer normalizes

theorem replacement_eq_intersection_sup_normal {group : Type*} [Group group]
    (subgroup normal : Subgroup group) [normal.Normal] (element : normal)
    (intersection_contains : subgroup ⊓ normal ≤ subgroup ⊓ conjugate subgroup element.val)
    (normalizes : conjugate subgroup element.val ≤ Subgroup.normalizer (subgroup : Set group)) :
    replacement subgroup element.val =
      (subgroup ⊓ conjugate subgroup element.val) ⊔ ((subgroup ⊔ conjugate subgroup element.val) ⊓ normal) := by
  let product := subgroup ⊔ conjugate subgroup element.val
  let commutators := firstCommutators subgroup element.val
  have commutators_le : commutators ≤ product ⊓ normal :=
    le_inf (firstCommutators_le_product subgroup element.val) (firstCommutators_le_normal subgroup normal element.property)
  apply le_antisymm (sup_le le_sup_left (commutators_le.trans le_sup_right))
  apply sup_le le_sup_left
  intro value value_mem
  have as_product : value ∈ (subgroup : Set group) * (commutators : Set group) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left subgroup commutators
      ((firstCommutators_le_product subgroup element.val).trans
        (product_normalizes_subgroup subgroup element.val normalizes)),
      ← product_eq_subgroup_sup_firstCommutators]
    exact value_mem.1
  obtain ⟨first, first_mem, second, second_mem, equal⟩ := as_product
  have first_normal : first ∈ normal := by
    have quotient_mem := normal.mul_mem value_mem.2 (normal.inv_mem (commutators_le second_mem).2)
    have cancel : value * second⁻¹ = first := by rw [← equal]; group
    rwa [cancel] at quotient_mem
  have first_intersection := intersection_contains ⟨first_mem, first_normal⟩
  rw [← equal]
  exact (replacement subgroup element.val).mul_mem
    ((show subgroup ⊓ conjugate subgroup element.val ≤ replacement subgroup element.val from le_sup_left) first_intersection)
    ((show commutators ≤ replacement subgroup element.val from le_sup_right) second_mem)

theorem product_normalizes_intersection {group : Type*} [Group group]
    (subgroup : Subgroup group) (element : group)
    (first_normalizes : subgroup ≤ Subgroup.normalizer (conjugate subgroup element : Set group))
    (second_normalizes : conjugate subgroup element ≤ Subgroup.normalizer (subgroup : Set group)) :
    subgroup ⊔ conjugate subgroup element ≤
      Subgroup.normalizer ((subgroup ⊓ conjugate subgroup element : Subgroup group) : Set group) := by
  apply le_trans _ Subgroup.inf_normalizer_le_normalizer_inf
  apply le_inf
  · exact sup_le Subgroup.le_normalizer second_normalizes
  · exact sup_le first_normalizes Subgroup.le_normalizer

theorem subgroup_inf_replacement {group : Type*} [Group group]
    (subgroup normal : Subgroup group) [normal.Normal] (element : normal)
    (intersection_contains : subgroup ⊓ normal ≤ subgroup ⊓ conjugate subgroup element.val)
    (first_normalizes : subgroup ≤ Subgroup.normalizer (conjugate subgroup element.val : Set group))
    (second_normalizes : conjugate subgroup element.val ≤ Subgroup.normalizer (subgroup : Set group)) :
    subgroup ⊓ replacement subgroup element.val = subgroup ⊓ conjugate subgroup element.val := by
  let product := subgroup ⊔ conjugate subgroup element.val
  let intersection := subgroup ⊓ conjugate subgroup element.val
  have product_normalizes := product_normalizes_intersection subgroup element.val first_normalizes second_normalizes
  apply le_antisymm
  · intro value value_mem
    have as_product : value ∈ (intersection : Set group) * ((product ⊓ normal : Subgroup group) : Set group) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left intersection (product ⊓ normal)
        (inf_le_left.trans product_normalizes),
        ← replacement_eq_intersection_sup_normal subgroup normal element intersection_contains second_normalizes]
      exact value_mem.2
    obtain ⟨first, first_mem, second, second_mem, equal⟩ := as_product
    have second_subgroup : second ∈ subgroup := by
      have quotient_mem := subgroup.mul_mem (subgroup.inv_mem first_mem.1) value_mem.1
      have cancel : first⁻¹ * value = second := by rw [← equal]; group
      rwa [cancel] at quotient_mem
    rw [← equal]
    exact intersection.mul_mem first_mem (intersection_contains ⟨second_subgroup, second_mem.2⟩)
  · exact le_inf inf_le_left le_sup_left

theorem product_eq_subgroup_sup_replacement {group : Type*} [Group group]
    (subgroup : Subgroup group) (element : group) :
    subgroup ⊔ conjugate subgroup element = subgroup ⊔ replacement subgroup element := by
  apply le_antisymm
  · rw [product_eq_subgroup_sup_firstCommutators]
    exact sup_le_sup_left (show firstCommutators subgroup element ≤ replacement subgroup element from le_sup_right) subgroup
  · exact sup_le le_sup_left (replacement_le_product subgroup element)

theorem card_replacement {group : Type*} [Group group] [Finite group]
    (subgroup normal : Subgroup group) [normal.Normal] (element : normal)
    (intersection_contains : subgroup ⊓ normal ≤ subgroup ⊓ conjugate subgroup element.val)
    (first_normalizes : subgroup ≤ Subgroup.normalizer (conjugate subgroup element.val : Set group))
    (second_normalizes : conjugate subgroup element.val ≤ Subgroup.normalizer (subgroup : Set group)) :
    Nat.card (replacement subgroup element.val) = Nat.card subgroup := by
  have conjugate_card : Nat.card (conjugate subgroup element.val) = Nat.card subgroup :=
    Subgroup.card_map_of_injective (MulAut.conj element.val⁻¹).injective
  have original_product := card_product_mul_card_intersection subgroup (conjugate subgroup element.val) first_normalizes
  have replacement_normalizes := (replacement_le_product subgroup element.val).trans
    (product_normalizes_subgroup subgroup element.val second_normalizes)
  have replaced_product := card_product_mul_card_intersection (replacement subgroup element.val) subgroup replacement_normalizes
  rw [sup_comm, ← product_eq_subgroup_sup_replacement, inf_comm,
    subgroup_inf_replacement subgroup normal element intersection_contains first_normalizes second_normalizes] at replaced_product
  rw [conjugate_card] at original_product
  apply mul_right_cancel₀ (Nat.card_pos (α := subgroup)).ne'
  rw [← replaced_product, original_product]

theorem replacement_maximum_order_abelian {group : Type*} [Group group] [Finite group]
    (subgroup normal : Subgroup group) [normal.Normal]
    (maximal : CFSG.OrderReductions.ThompsonCenter.MaximumOrderAbelian group subgroup)
    (central : commutator normal ≤ Subgroup.center normal) (odd_order : Odd (Nat.card normal))
    (derived_le : ⁅normal, normal⁆ ≤ subgroup) (element : normal)
    (first_normalizes : subgroup ≤ Subgroup.normalizer (conjugate subgroup element.val : Set group))
    (second_normalizes : conjugate subgroup element.val ≤ Subgroup.normalizer (subgroup : Set group)) :
    CFSG.OrderReductions.ThompsonCenter.MaximumOrderAbelian group (replacement subgroup element.val) := by
  have : IsMulCommutative subgroup := maximal.1
  refine ⟨replacement_abelian subgroup normal central odd_order derived_le element first_normalizes second_normalizes, ?_⟩
  intro other abelian
  rw [card_replacement subgroup normal element
    (intersection_le_conjugate_intersection subgroup normal derived_le element.property) first_normalizes second_normalizes]
  exact maximal.2 other abelian

end CFSG.OrderReductions.ReplacementGeometry
