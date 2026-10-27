module

public import CFSG.Assembly.OrderReductions.NormalizerAuxiliary

public section

namespace CFSG.OrderReductions.OutsideCentralizer

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.NormalizerAuxiliary

theorem inversionSet_invariant {group : Type*} [Group group]
    (subgroup : Subgroup group) (involution : Involution group)
    (normalizes : involution.val ∈ Subgroup.normalizer (subgroup : Set group)) :
    MulAut.conj involution.val '' inversionSet subgroup involution = inversionSet subgroup involution := by
  let automorphism := MulAut.conj involution.val
  have involutive := CFSG.OrderReductions.PrimeRegular.involution_conjugation_involutive involution
  have maps : ∀ element ∈ inversionSet subgroup involution,
      automorphism element ∈ inversionSet subgroup involution := by
    intro element element_mem
    refine ⟨(Subgroup.mem_normalizer_iff.mp normalizes element).mp element_mem.1, ?_⟩
    rw [involutive, element_mem.2, inv_inv]
  apply Set.Subset.antisymm
  · rintro element ⟨original, original_mem, image_eq⟩
    exact image_eq ▸ maps original original_mem
  · intro element element_mem
    exact ⟨automorphism element, maps element element_mem, involutive element⟩

theorem involution_normalizes_centralizer {group : Type*} [Group group]
    (subgroup : Subgroup group) (involution : Involution group)
    (normalizes : involution.val ∈ Subgroup.normalizer (subgroup : Set group)) :
    involution.val ∈ Subgroup.normalizer
      (↑(Subgroup.centralizer (inversionSet subgroup involution)) : Set group) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (Subgroup.centralizer (inversionSet subgroup involution)).map
    (MulAut.conj involution.val).toMonoidHom = Subgroup.centralizer (inversionSet subgroup involution)
  rw [← centralizer_image_eq, inversionSet_invariant subgroup involution normalizes]

theorem noncentral_involution_not_inversion_centralizer {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (odd_subgroup : Odd (Nat.card subgroup))
    (involution : Involution group)
    (normalizes : involution.val ∈ Subgroup.normalizer (subgroup : Set group))
    (noncentral : ¬ subgroup ≤ Subgroup.centralizer ({involution.val} : Set group)) :
    involution.val ∉ Subgroup.centralizer (inversionSet subgroup involution) := by
  classical
  obtain ⟨element, element_mem, not_commuting⟩ : ∃ element ∈ subgroup,
      involution.val * element * involution.val⁻¹ ≠ element := by
    by_contra no_element
    push Not at no_element
    apply noncentral
    intro element element_mem
    apply Subgroup.mem_centralizer_iff.mpr
    intro other other_mem
    have other_eq : other = involution.val := by simpa only [Set.mem_singleton_iff] using other_mem
    rw [other_eq]
    exact mul_inv_eq_iff_eq_mul.mp (no_element element element_mem)
  let automorphism := MulAut.conj involution.val
  let inverted := element * (automorphism element)⁻¹
  have inverted_mem : inverted ∈ subgroup :=
    subgroup.mul_mem element_mem
      (subgroup.inv_mem ((Subgroup.mem_normalizer_iff.mp normalizes element).mp element_mem))
  have inverted_inverted : automorphism inverted = inverted⁻¹ := by
    change automorphism (element * (automorphism element)⁻¹) = (element * (automorphism element)⁻¹)⁻¹
    rw [map_mul, map_inv, CFSG.OrderReductions.PrimeRegular.involution_conjugation_involutive,
      mul_inv_rev, inv_inv]
  have inverted_ne_one : inverted ≠ 1 := by
    intro inverted_one
    exact not_commuting (mul_inv_eq_one.mp inverted_one).symm
  intro centralizes
  have commuting := Subgroup.mem_centralizer_iff.mp centralizes inverted ⟨inverted_mem, inverted_inverted⟩
  have fixed : automorphism inverted = inverted := by
    change involution.val * inverted * involution.val⁻¹ = inverted
    rw [← commuting, mul_assoc, mul_inv_cancel, mul_one]
  have square_one : inverted ^ 2 = 1 := by
    have inverse_eq : inverted⁻¹ = inverted := inverted_inverted.symm.trans fixed
    rw [pow_two]
    calc
      inverted * inverted = inverted⁻¹ * inverted := congrArg (fun first => first * inverted) inverse_eq.symm
      _ = 1 := inv_mul_cancel inverted
  have order_divides_two := orderOf_dvd_of_pow_eq_one square_one
  have odd_order := odd_subgroup.of_dvd_nat (subgroup.orderOf_dvd_natCard inverted_mem)
  have order_one : orderOf inverted = 1 := Nat.dvd_one.mp
    ((Nat.dvd_gcd order_divides_two (dvd_refl (orderOf inverted))).trans
      (by rw [odd_order.coprime_two_left.gcd_eq_one]))
  exact inverted_ne_one (orderOf_eq_one_iff.mp order_one)

theorem odd_normal_of_excluded_involution {group : Type*} [Group group] [Finite group]
    (ambient : Subgroup group) (strong : StronglyEmbedded ambient)
    (normal : Subgroup group) [normal.Normal]
    (involution : Involution group) (excluded : involution.val ∉ normal) :
    Odd (Nat.card normal) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  by_contra not_odd
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2
    (Nat.not_odd_iff_even.mp not_odd).two_dvd
  let internal : Involution group :=
    ⟨element.val, (Subgroup.orderOf_coe element).trans element_order⟩
  obtain ⟨conjugator, conjugates⟩ := CFSG.OrderReductions.InvolutionFusion.all_involutions_conjugate_of_disconnected
    (stronglyEmbedded_not_preconnected ambient strong) internal involution
  have conjugate_mem := (inferInstance : normal.Normal).conj_mem internal.val element.property conjugator
  have equal_values : conjugator * internal.val * conjugator⁻¹ = involution.val :=
    congrArg Subtype.val conjugates
  exact excluded (equal_values ▸ conjugate_mem)

theorem inversion_centralizer_odd {group : Type*} [Group group] [Finite group]
    (ambient : Subgroup group) (strong : StronglyEmbedded ambient)
    (subgroup : Subgroup group) (odd_subgroup : Odd (Nat.card subgroup))
    (involution : Involution group) (mem_ambient : involution.val ∈ ambient)
    (normalizes : involution.val ∈ Subgroup.normalizer (subgroup : Set group))
    (noncentral : ¬ subgroup ≤ Subgroup.centralizer ({involution.val} : Set group))
    (crosses : ¬ Subgroup.centralizer (inversionSet subgroup involution) ≤ ambient) :
    Odd (Nat.card (Subgroup.centralizer (inversionSet subgroup involution))) := by
  let centralizer := Subgroup.centralizer (inversionSet subgroup involution)
  let overgroup := centralizer ⊔ Subgroup.zpowers involution.val
  have mem_overgroup : involution.val ∈ overgroup :=
    (show Subgroup.zpowers involution.val ≤ overgroup from le_sup_right)
      (Subgroup.mem_zpowers involution.val)
  have excluded := noncentral_involution_not_inversion_centralizer subgroup odd_subgroup
    involution normalizes noncentral
  have overgroup_crosses : ¬ overgroup ≤ ambient := fun contains => crosses (le_sup_left.trans contains)
  have even_intersection : Even (Nat.card ↥(ambient ⊓ overgroup)) := by
    apply even_iff_two_dvd.mpr
    have divides := Subgroup.orderOf_dvd_natCard (ambient ⊓ overgroup) ⟨mem_ambient, mem_overgroup⟩
    rwa [involution.property] at divides
  have strong_internal := CFSG.OrderReductions.StrongEmbeddingInheritance.intersection_stronglyEmbedded
    ambient strong overgroup overgroup_crosses even_intersection
  have cyclic_normalizes : Subgroup.zpowers involution.val ≤ Subgroup.normalizer (centralizer : Set group) :=
    Subgroup.zpowers_le.mpr (involution_normalizes_centralizer subgroup involution normalizes)
  have : (centralizer.subgroupOf overgroup).Normal := by
    change (centralizer.subgroupOf (centralizer ⊔ Subgroup.zpowers involution.val)).Normal
    rw [sup_comm]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer cyclic_normalizes
  let internal : Involution overgroup :=
    ⟨⟨involution.val, mem_overgroup⟩, by rw [← Subgroup.orderOf_coe]; exact involution.property⟩
  have odd_internal := odd_normal_of_excluded_involution (ambient.subgroupOf overgroup) strong_internal
    (centralizer.subgroupOf overgroup) internal excluded
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show centralizer ≤ overgroup from le_sup_left)).toEquiv] at odd_internal

end CFSG.OrderReductions.OutsideCentralizer
