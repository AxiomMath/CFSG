module

public import CFSG.Assembly.OrderReductions.OddKernelInvolutions
public import CFSG.Assembly.OrderReductions.NormalizerAuxiliary

public section

namespace CFSG.OrderReductions.NormalizerQuotient

open CFSG.OrderReductions.InvolutionGraph

theorem commuting_pair_survives_odd_kernel {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (odd_kernel : Odd (Nat.card homomorphism.ker))
    (first second : Involution source) (distinct : first ≠ second)
    (commutes : Commute first.val second.val) :
    ∃ first_image second_image : Involution target,
      first_image.val = homomorphism first.val ∧ second_image.val = homomorphism second.val ∧
        first_image ≠ second_image ∧ Commute first_image.val second_image.val := by
  let first_image : Involution target :=
    ⟨homomorphism first.val, CFSG.OrderReductions.OddKernelInvolutions.involution_image_order homomorphism odd_kernel first⟩
  let second_image : Involution target :=
    ⟨homomorphism second.val, CFSG.OrderReductions.OddKernelInvolutions.involution_image_order homomorphism odd_kernel second⟩
  refine ⟨first_image, second_image, rfl, rfl, ?_, commutes.map homomorphism⟩
  intro equal
  have equal_images : homomorphism first.val = homomorphism second.val := congrArg Subtype.val equal
  have product_kernel : first.val * second.val ∈ homomorphism.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, equal_images]
    have square := CFSG.OrderReductions.InvolutionFusion.involution_mul_self second
    have image_square := congrArg homomorphism square
    simpa only [map_mul, map_one] using image_square
  have divides := homomorphism.ker.orderOf_dvd_natCard product_kernel
  rw [CFSG.OrderReductions.RankTwoContainment.commuting_involution_product first second distinct commutes] at divides
  exact odd_kernel.not_two_dvd_nat divides

theorem quotient_card_lt_of_nontrivial {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (normal : Subgroup group) [normal.Normal]
    (normal_le : normal ≤ subgroup) (nontrivial : normal ≠ ⊥) :
    Nat.card (subgroup ⧸ normal.subgroupOf subgroup) < Nat.card group := by
  have normal_card : 1 < Nat.card (normal.subgroupOf subgroup) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe normal_le).toEquiv]
    have card_ne_one : Nat.card normal ≠ 1 := fun equal => nontrivial (Subgroup.card_eq_one.mp equal)
    have card_positive : 0 < Nat.card normal := Nat.card_pos
    omega
  have quotient_positive : 0 < Nat.card (subgroup ⧸ normal.subgroupOf subgroup) := Nat.card_pos
  have product_eq := (normal.subgroupOf subgroup).card_mul_index
  rw [Subgroup.index_eq_card] at product_eq
  have card_lt : Nat.card (subgroup ⧸ normal.subgroupOf subgroup) < Nat.card subgroup := by
    nlinarith
  exact card_lt.trans_le subgroup.card_le_card_group

theorem normalizer_quotient_card_lt {group : Type*} [Group group] [Finite group]
    (normal : Subgroup group) (nontrivial : normal ≠ ⊥) :
    Nat.card ((Subgroup.normalizer (normal : Set group)) ⧸
      normal.subgroupOf (Subgroup.normalizer (normal : Set group))) < Nat.card group := by
  let normalizer := Subgroup.normalizer (normal : Set group)
  have internal_nontrivial : normal.subgroupOf normalizer ≠ ⊥ := by
    intro equal_bot
    have image_eq := congrArg (Subgroup.map normalizer.subtype) equal_bot
    rw [Subgroup.map_subgroupOf_eq_of_le normal.le_normalizer, Subgroup.map_bot] at image_eq
    exact nontrivial image_eq
  have internal_card : 1 < Nat.card (normal.subgroupOf normalizer) := by
    have not_one : Nat.card (normal.subgroupOf normalizer) ≠ 1 :=
      fun equal => internal_nontrivial (Subgroup.card_eq_one.mp equal)
    have positive : 0 < Nat.card (normal.subgroupOf normalizer) := Nat.card_pos
    omega
  have product_eq := (normal.subgroupOf normalizer).card_mul_index
  rw [Subgroup.index_eq_card] at product_eq
  have quotient_positive : 0 < Nat.card (normalizer ⧸ normal.subgroupOf normalizer) := Nat.card_pos
  have card_lt : Nat.card (normalizer ⧸ normal.subgroupOf normalizer) < Nat.card normalizer := by nlinarith
  exact card_lt.trans_le normalizer.card_le_card_group

theorem pair_le_normalizer {group : Type*} [Group group]
    (first second : Component group) (normal : Subgroup group)
    (contains : normal ≤ CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
    [(normal.subgroupOf (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)).Normal] :
    CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second ≤ Subgroup.normalizer (normal : Set group) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer contains).mp inferInstance

theorem all_point_involutions_normalize {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second)
    (normal : Subgroup group) (contains : normal ≤ CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
    [(normal.subgroupOf (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)).Normal]
    (inside : Involution group) (inside_mem : inside.val ∈ componentStabilizer first)
    (inside_normalizes : inside.val ∈ Subgroup.normalizer (normal : Set group))
    (involution : Involution group) (mem_first : involution.val ∈ componentStabilizer first) :
    involution.val ∈ Subgroup.normalizer (normal : Set group) := by
  obtain ⟨conjugator, conjugates⟩ := CFSG.OrderReductions.PrimeRegular.pair_conjugates_involutions
    first second distinct inside involution inside_mem mem_first
  have conjugator_normalizes := pair_le_normalizer first second normal contains conjugator.property
  have conjugate_mem := (Subgroup.normalizer (normal : Set group)).mul_mem
    ((Subgroup.normalizer (normal : Set group)).mul_mem conjugator_normalizes inside_normalizes)
    ((Subgroup.normalizer (normal : Set group)).inv_mem conjugator_normalizes)
  have equal_values : conjugator.val * inside.val * conjugator.val⁻¹ = involution.val :=
    congrArg Subtype.val conjugates
  exact equal_values ▸ conjugate_mem

theorem normalizer_intersection_strong {group : Type*} [Group group] [Finite group]
    (point : Component group) (strong : StronglyEmbedded (componentStabilizer point))
    (normal : Subgroup group) (inside outside : Involution group)
    (inside_mem : inside.val ∈ componentStabilizer point)
    (outside_not_mem : outside.val ∉ componentStabilizer point)
    (inside_normalizes : inside.val ∈ Subgroup.normalizer (normal : Set group))
    (outside_normalizes : outside.val ∈ Subgroup.normalizer (normal : Set group)) :
    StronglyEmbedded ((componentStabilizer point).subgroupOf (Subgroup.normalizer (normal : Set group))) := by
  apply CFSG.OrderReductions.NormalizerAuxiliary.normalizer_intersection_stronglyEmbedded point strong normal
    inside inside_mem inside_normalizes
  intro contains
  exact outside_not_mem (contains outside_normalizes)

end CFSG.OrderReductions.NormalizerQuotient
