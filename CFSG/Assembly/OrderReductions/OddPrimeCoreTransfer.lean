module

public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.RegularCore

public section

namespace CFSG.OrderReductions.OddPrimeCoreTransfer

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.PrimeComplementCore

theorem twisted_product_involution {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (odd_subgroup : Odd (Nat.card subgroup))
    (involution : Involution group) (element : subgroup)
    (inverted : (MulAut.conj involution.val) element.val = element.val⁻¹) :
    orderOf (element.val * involution.val) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply orderOf_eq_prime
  · have conjugation_eq : involution.val * element.val * involution.val = element.val⁻¹ := by
      change involution.val * element.val * involution.val⁻¹ = element.val⁻¹ at inverted
      rwa [inv_eq_self_of_orderOf_eq_two involution.property] at inverted
    calc
      (element.val * involution.val) ^ 2 =
          element.val * (involution.val * element.val * involution.val) := by rw [pow_two]; group
      _ = 1 := by rw [conjugation_eq, mul_inv_cancel]
  · intro product_one
    have equal_values : element.val = involution.val := by
      have equal_inverse := mul_eq_one_iff_eq_inv.mp product_one
      rwa [inv_eq_self_of_orderOf_eq_two involution.property] at equal_inverse
    have divides := subgroup.orderOf_dvd_natCard element.property
    rw [equal_values, involution.property] at divides
    exact odd_subgroup.not_two_dvd_nat divides

theorem normalized_core_transfer {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (ambient : Subgroup group) (strong : StronglyEmbedded ambient)
    (odd_subgroup : Subgroup group) (odd_order : Odd (Nat.card odd_subgroup))
    (involution : Involution group) (mem_ambient : involution.val ∈ ambient)
    (odd_invariant : odd_subgroup.map (MulAut.conj involution.val).toMonoidHom = odd_subgroup)
    (prime_subgroup : Subgroup group) (prime_group : IsPGroup prime prime_subgroup)
    (prime_le_odd : prime_subgroup ≤ odd_subgroup) (prime_le_ambient : prime_subgroup ≤ ambient)
    (prime_invariant : prime_subgroup.map (MulAut.conj involution.val).toMonoidHom = prime_subgroup)
    (inverted_set : Set group) (set_le_prime : inverted_set ⊆ prime_subgroup)
    (set_inverted : ∀ element ∈ inverted_set,
      (MulAut.conj involution.val) element = element⁻¹)
    (centralizer_le : Subgroup.centralizer inverted_set ⊓ odd_subgroup ≤ ambient) :
    ambientCore prime odd_subgroup ≤ ambientCore prime (ambient ⊓ odd_subgroup) := by
  let core := ambientCore prime odd_subgroup
  have core_odd : Odd (Nat.card core) :=
    odd_order.of_dvd_nat (Subgroup.card_dvd_of_le (ambientCore_le prime odd_subgroup))
  have odd_normalizes : odd_subgroup ≤ Subgroup.normalizer (core : Set group) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (ambientCore_le prime odd_subgroup)).mp
      (ambientCore_normal_in_subgroup prime odd_subgroup)
  have action_invariant : ∀ acting : prime_subgroup,
      core.map (MulAut.conj acting.val).toMonoidHom = core :=
    fun acting => Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (odd_normalizes (prime_le_odd acting.property))
  have core_invariant : core.map (MulAut.conj involution.val).toMonoidHom = core :=
    CFSG.OrderReductions.RegularCore.ambientCore_invariant prime (MulAut.conj involution.val)
      odd_subgroup odd_invariant
  let action : prime_subgroup →* MulAut core := CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism
    (MulAut.conj.comp prime_subgroup.subtype) core action_invariant
  let actor_automorphism := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism
    (MulAut.conj involution.val) prime_subgroup prime_invariant
  let automorphism := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism
    (MulAut.conj involution.val) core core_invariant
  have actor_involutive := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive
    (MulAut.conj involution.val) (CFSG.OrderReductions.PrimeRegular.involution_conjugation_involutive involution)
      prime_subgroup prime_invariant
  have involutive := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive
    (MulAut.conj involution.val) (CFSG.OrderReductions.PrimeRegular.involution_conjugation_involutive involution)
      core core_invariant
  have compatible : ∀ acting : prime_subgroup, ∀ element : core,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element) := by
    intro acting element
    apply Subtype.ext
    change involution.val * (acting.val * element.val * acting.val⁻¹) * involution.val⁻¹ =
      (involution.val * acting.val * involution.val⁻¹) *
        (involution.val * element.val * involution.val⁻¹) *
          (involution.val * acting.val * involution.val⁻¹)⁻¹
    group
  have core_le_ambient : core ≤ ambient := by
    apply Subgroup.subgroupOf_eq_top.mp
    apply CFSG.OrderReductions.InvertedSubgroup.odd_prime_involution_generation prime prime_group
      (ambientCore_coprime prime odd_subgroup) core_odd action actor_automorphism actor_involutive
        automorphism involutive compatible
    · intro element fixed
      apply centralizer_le
      refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, ambientCore_le prime odd_subgroup element.property⟩
      intro acting acting_mem
      let actor_element : prime_subgroup := ⟨acting, set_le_prime acting_mem⟩
      have actor_inverted : actor_automorphism actor_element = actor_element⁻¹ :=
        Subtype.ext (set_inverted acting acting_mem)
      have element_fixed := congrArg Subtype.val (fixed actor_element actor_inverted)
      change acting * element.val * acting⁻¹ = element.val at element_fixed
      exact mul_inv_eq_iff_eq_mul.mp element_fixed
    · intro acting acting_inverted element element_fixed
      have inverted : (MulAut.conj involution.val) acting.val = acting.val⁻¹ :=
        congrArg Subtype.val acting_inverted
      have prime_odd : Odd (Nat.card prime_subgroup) :=
        odd_order.of_dvd_nat (Subgroup.card_dvd_of_le prime_le_odd)
      let product_involution : Involution group :=
        ⟨acting.val * involution.val,
          twisted_product_involution prime_subgroup prime_odd involution acting inverted⟩
      apply stronglyEmbedded_centralizer_le ambient strong product_involution
        (ambient.mul_mem (prime_le_ambient acting.property) mem_ambient)
      apply Subgroup.mem_centralizer_iff.mpr
      intro other other_mem
      have other_eq : other = acting.val * involution.val := by
        simpa only [Set.mem_singleton_iff] using other_mem
      rw [other_eq]
      have conjugation_fixed := congrArg Subtype.val element_fixed
      change acting.val * (involution.val * element.val * involution.val⁻¹) * acting.val⁻¹ =
        element.val at conjugation_fixed
      change (acting.val * involution.val) * element.val = element.val * (acting.val * involution.val)
      apply mul_inv_eq_iff_eq_mul.mp
      simpa only [mul_inv_rev, mul_assoc] using conjugation_fixed
  have core_le_intersection : core ≤ ambient ⊓ odd_subgroup :=
    le_inf core_le_ambient (ambientCore_le prime odd_subgroup)
  have intersection_normalizes : ambient ⊓ odd_subgroup ≤ Subgroup.normalizer (core : Set group) :=
    inf_le_right.trans odd_normalizes
  have : (core.subgroupOf (ambient ⊓ odd_subgroup)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer core_le_intersection).mpr intersection_normalizes
  exact normal_le_ambientCore prime core (ambient ⊓ odd_subgroup) core_le_intersection
    (ambientCore_coprime prime odd_subgroup)

theorem component_three_point_core_transfer {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Component group)
    (distinct : first ≠ second) (involution : Involution group)
    (mem_first : involution.val ∈ componentStabilizer first)
    (inverted_set : Set group) (prime_subgroup : Subgroup group)
    (prime_generated : prime_subgroup = Subgroup.closure inverted_set)
    (prime_group : IsPGroup prime prime_subgroup)
    (prime_le_pair : prime_subgroup ≤ CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
    (set_inverted : ∀ element ∈ inverted_set,
      (MulAut.conj involution.val) element = element⁻¹)
    (centralizer_le : Subgroup.centralizer inverted_set ⊓
      CFSG.OrderReductions.InvolutiveIntersection.intersection (MulAut.conj involution.val)
        (componentStabilizer second) ≤ componentStabilizer first) :
    ambientCore prime (CFSG.OrderReductions.InvolutiveIntersection.intersection (MulAut.conj involution.val)
      (componentStabilizer second)) ≤
        ambientCore prime (componentStabilizer first ⊓
          CFSG.OrderReductions.InvolutiveIntersection.intersection (MulAut.conj involution.val)
            (componentStabilizer second)) := by
  let automorphism := MulAut.conj involution.val
  let pair := CFSG.OrderReductions.InvolutiveIntersection.intersection automorphism (componentStabilizer second)
  have involutive := CFSG.OrderReductions.PrimeRegular.involution_conjugation_involutive involution
  have moved_ne_second : second ≠ involution.val • second := by
    intro fixed
    have same := CFSG.OrderReductions.MaximalThreePoint.involution_fixed_component_unique involution first second
      mem_first fixed.symm
    exact distinct same
  have odd_pair : Odd (Nat.card pair) := by
    change Odd (Nat.card ↥(componentStabilizer second ⊓
      (componentStabilizer second).map automorphism.toMonoidHom))
    rw [← componentStabilizer_smul]
    exact distinct_componentStabilizers_odd_intersection second _ moved_ne_second
  have set_le_prime : inverted_set ⊆ prime_subgroup := by
    rw [prime_generated]
    exact Subgroup.subset_closure
  have prime_invariant : prime_subgroup.map automorphism.toMonoidHom = prime_subgroup := by
    have image_le : prime_subgroup.map automorphism.toMonoidHom ≤ prime_subgroup := by
      apply Subgroup.map_le_iff_le_comap.mpr
      rw [prime_generated]
      apply (Subgroup.closure_le _).mpr
      intro element element_mem
      change automorphism element ∈ Subgroup.closure inverted_set
      rw [set_inverted element element_mem]
      exact (Subgroup.closure inverted_set).inv_mem (Subgroup.subset_closure element_mem)
    apply Subgroup.eq_of_le_of_card_ge image_le
    rw [Subgroup.card_map_of_injective automorphism.injective]
  have prime_le_pair_intersection : prime_subgroup ≤ pair :=
    CFSG.OrderReductions.InvolutiveIntersection.invariant_le_intersection automorphism
      (componentStabilizer second) prime_subgroup (fun element membership =>
        (prime_le_pair membership).2) prime_invariant
  exact normalized_core_transfer prime (componentStabilizer first)
    (componentStabilizer_stronglyEmbedded first ⟨second, distinct.symm⟩) pair odd_pair involution mem_first
    (CFSG.OrderReductions.InvolutiveIntersection.intersection_invariant automorphism involutive _)
    prime_subgroup prime_group prime_le_pair_intersection
    (fun element membership => (prime_le_pair membership).1) prime_invariant
    inverted_set set_le_prime set_inverted centralizer_le

end CFSG.OrderReductions.OddPrimeCoreTransfer
