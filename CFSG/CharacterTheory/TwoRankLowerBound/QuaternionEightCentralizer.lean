module

public import CFSG.CharacterTheory.TwoRankLowerBound.RootProjection
public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionEightFusion

public section

open scoped Classical Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

theorem two_element_isConj_sylow {G : Type*} [Group G] [Finite G]
    (sylow : Sylow 2 G) (element : G) (horder : ∃ exponent, orderOf element = 2 ^ exponent) :
    ∃ member : (sylow : Subgroup G), IsConj element (member : G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpgroup : IsPGroup 2 (Subgroup.zpowers element) := by
    obtain ⟨exponent, hexponent⟩ := horder
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hexponent])
  obtain ⟨otherSylow, hle⟩ := hpgroup.exists_le_sylow
  obtain ⟨conjugator, hconjugator⟩ := MulAction.exists_smul_eq G otherSylow sylow
  have hmember : conjugator * element * conjugator⁻¹ ∈ (sylow : Subgroup G) := by
    rw [← hconjugator]
    change conjugator * element * conjugator⁻¹ ∈ ((conjugator • otherSylow : Sylow 2 G) : Set G)
    rw [Sylow.coe_smul]
    exact ⟨element, hle (Subgroup.mem_zpowers element), rfl⟩
  exact ⟨⟨_, hmember⟩, isConj_iff.mpr ⟨conjugator, rfl⟩⟩

theorem quaternionEight_unique_involution (element : QuaternionGroup 2)
    (horder : orderOf element = 2) : element = QuaternionGroup.a (2 : ZMod 4) := by
  rcases quaternionEight_element_class element with hone | hinvolution | ⟨label, hrepresentative⟩
  · rw [hone, orderOf_one] at horder
    omega
  · exact hinvolution
  · rcases hrepresentative with hrepresentative | hinverse
    · rw [hrepresentative, quaternionEight_representative_order] at horder
      omega
    · rw [hinverse, orderOf_inv, quaternionEight_representative_order] at horder
      omega

theorem quaternionEight_four_square (element : QuaternionGroup 2)
    (horder : orderOf element = 4) : element ^ 2 = QuaternionGroup.a (2 : ZMod 4) := by
  apply quaternionEight_unique_involution
  rw [orderOf_pow, horder]
  norm_num

theorem unique_involution_mem_center {G : Type*} [Group G]
    (involution : G) (horder : orderOf involution = 2)
    (hunique : ∀ other : G, orderOf other = 2 → other = involution) :
    involution ∈ Subgroup.center G := by
  apply Subgroup.mem_center_iff.mpr
  intro member
  have hequal : member * involution * member⁻¹ = involution :=
    hunique _ ((MulAut.conj member).orderOf_eq involution |>.trans horder)
  exact (mul_inv_eq_iff_eq_mul).mp hequal

theorem sylow_quaternion_eight_involution_data {G : Type*} [Group G]
    (sylow : Sylow 2 G) (isomorphism : (sylow : Subgroup G) ≃* QuaternionGroup 2) :
    let involution := isomorphism.symm (QuaternionGroup.a (2 : ZMod 4))
    orderOf (involution : G) = 2 ∧
      (∀ other : G, other ∈ sylow → orderOf other = 2 → other = involution) ∧
      (sylow : Subgroup G) ≤ Subgroup.centralizer ({(involution : G)} : Set G) := by
  intro involution
  have horder : orderOf involution = 2 :=
    (isomorphism.symm.orderOf_eq _).trans quaternionEight_involution_order
  have hunique : ∀ other : (sylow : Subgroup G), orderOf other = 2 → other = involution := by
    intro other hother
    apply isomorphism.injective
    rw [MulEquiv.apply_symm_apply]
    exact quaternionEight_unique_involution _ ((isomorphism.orderOf_eq other).trans hother)
  refine ⟨(Subgroup.orderOf_coe involution).trans horder, ?_, ?_⟩
  · intro other hmember hother
    exact congrArg Subtype.val (hunique ⟨other, hmember⟩
      ((Subgroup.orderOf_coe ⟨other, hmember⟩).symm.trans hother))
  · intro member hmember
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp
        (unique_involution_mem_center involution horder hunique) ⟨member, hmember⟩))

theorem sylow_quaternion_eight_centralizer_unique_involution {G : Type*}
    [Group G] [Finite G] (sylow : Sylow 2 G)
    (isomorphism : (sylow : Subgroup G) ≃* QuaternionGroup 2) :
    let involution := isomorphism.symm (QuaternionGroup.a (2 : ZMod 4))
    ∀ other : G, other ∈ Subgroup.centralizer ({(involution : G)} : Set G) →
      orderOf other = 2 → other = involution := by
  intro involution
  obtain ⟨horder, hunique, hle⟩ := sylow_quaternion_eight_involution_data sylow isomorphism
  let centralizer := Subgroup.centralizer ({(involution : G)} : Set G)
  let localSylow := sylow.subtype hle
  let localInvolution : centralizer := ⟨involution, hle involution.property⟩
  have hcentral : localInvolution ∈ Subgroup.center centralizer := by
    apply Subgroup.mem_center_iff.mpr
    intro member
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp member.property)
  intro other hmember hother
  let localOther : centralizer := ⟨other, hmember⟩
  have hlocalOrder : orderOf localOther = 2 := (Subgroup.orderOf_coe localOther).symm.trans hother
  obtain ⟨member, hconj⟩ := two_element_isConj_sylow localSylow localOther
    ⟨1, by simpa only [pow_one] using hlocalOrder⟩
  have hmemberOriginal : ((member : centralizer) : G) ∈ sylow := by
    change ((member : centralizer) : G) ∈ (sylow : Subgroup G)
    have hmember := member.property
    change (member : centralizer) ∈ (localSylow : Subgroup centralizer) at hmember
    simpa only [localSylow, Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hmember
  have hmemberOrder : orderOf ((member : centralizer) : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact (orderOf_eq_of_isConj hconj).symm.trans hlocalOrder
  have hequal : (member : centralizer) = localInvolution :=
    Subtype.ext (hunique _ hmemberOriginal hmemberOrder)
  rw [hequal] at hconj
  exact congrArg Subtype.val (hconj.eq_of_right_mem_center hcentral)

theorem cyclicRootSet_iff_even_order_of_unique_involution {G : Type*}
    [Group G] [Finite G] (involution : G) (horder : orderOf involution = 2)
    (hunique : ∀ other : G, orderOf other = 2 → other = involution) (element : G) :
    element ∈ cyclicRootSet involution ↔ Even (orderOf element) := by
  constructor
  · intro hroot
    exact even_iff_two_dvd.mpr (horder ▸ orderOf_dvd_of_mem_zpowers hroot)
  · intro heven
    let power := element ^ (orderOf element / 2)
    have hpowerOrder : orderOf power = 2 := orderOf_pow_orderOf_div
      (orderOf_pos element |>.ne') (even_iff_two_dvd.mp heven)
    have hequal := hunique power hpowerOrder
    change involution ∈ Subgroup.zpowers element
    rw [← hequal]
    exact (Subgroup.zpowers element).pow_mem (Subgroup.mem_zpowers element) _

theorem sylow_quaternion_eight_root_support {G : Type*} [Group G] [Finite G]
    (sylow : Sylow 2 G) (isomorphism : (sylow : Subgroup G) ≃* QuaternionGroup 2) :
    let involution := isomorphism.symm (QuaternionGroup.a (2 : ZMod 4))
    ∀ element : G, element ∈ cyclicRootSet (involution : G) ↔
      element ∈ Subgroup.centralizer ({(involution : G)} : Set G) ∧ Even (orderOf element) := by
  intro involution element
  let centralizer := Subgroup.centralizer ({(involution : G)} : Set G)
  have hdata := sylow_quaternion_eight_involution_data sylow isomorphism
  have hunique := sylow_quaternion_eight_centralizer_unique_involution sylow isomorphism
  constructor
  · intro hroot
    refine ⟨cyclicRootSet_subset_centralizer _ hroot, ?_⟩
    exact even_iff_two_dvd.mpr (hdata.1 ▸ orderOf_dvd_of_mem_zpowers hroot)
  · rintro ⟨hmember, heven⟩
    let localInvolution : centralizer := ⟨involution, hdata.2.2 involution.property⟩
    let localElement : centralizer := ⟨element, hmember⟩
    have hlocalOrder : orderOf localInvolution = 2 :=
      (Subgroup.orderOf_coe localInvolution).symm.trans hdata.1
    have hlocalUnique : ∀ other : centralizer, orderOf other = 2 → other = localInvolution := by
      intro other hother
      exact Subtype.ext (hunique other other.property ((Subgroup.orderOf_coe other).trans hother))
    have hroot := (cyclicRootSet_iff_even_order_of_unique_involution localInvolution
      hlocalOrder hlocalUnique localElement).mpr
      (by rw [← Subgroup.orderOf_coe localElement]; exact heven)
    exact (mem_zpowers_of_injective_iff centralizer.subtype centralizer.subtype_injective
      localInvolution localElement).mpr hroot

theorem sylow_quaternion_eight_centralizer_ne_top_of_simple {G : Type*}
    [Group G] [IsSimpleGroup G] (hnonabelian : ∃ left right : G, left * right ≠ right * left)
    (sylow : Sylow 2 G) (isomorphism : (sylow : Subgroup G) ≃* QuaternionGroup 2) :
    let involution := isomorphism.symm (QuaternionGroup.a (2 : ZMod 4))
    Subgroup.centralizer ({(involution : G)} : Set G) ≠ ⊤ := by
  intro involution htop
  have hcentral := (Subgroup.centralizer_eq_top_iff_subset.mp htop) (Set.mem_singleton _)
  rw [center_eq_bot_of_nonabelian_simple G hnonabelian] at hcentral
  change (involution : G) = 1 at hcentral
  have horder := (sylow_quaternion_eight_involution_data sylow isomorphism).1
  rw [hcentral, orderOf_one] at horder
  omega

theorem sylow_quaternion_eight_four_square {G : Type*} [Group G]
    (sylow : Sylow 2 G) (isomorphism : (sylow : Subgroup G) ≃* QuaternionGroup 2)
    (element : (sylow : Subgroup G)) (horder : orderOf element = 4) :
    element ^ 2 = isomorphism.symm (QuaternionGroup.a (2 : ZMod 4)) := by
  apply isomorphism.injective
  rw [map_pow, MulEquiv.apply_symm_apply]
  exact quaternionEight_four_square _ ((isomorphism.orderOf_eq element).trans horder)

theorem sylow_quaternion_eight_centralizer_four_fusion {G : Type*}
    [Group G] [Finite G] [Group.IsPerfect G] (sylow : Sylow 2 G)
    (isomorphism : (sylow : Subgroup G) ≃* QuaternionGroup 2) :
    let involution := isomorphism.symm (QuaternionGroup.a (2 : ZMod 4))
    let centralizer := Subgroup.centralizer ({(involution : G)} : Set G)
    ∀ left right : (sylow : Subgroup G), orderOf left = 4 → orderOf right = 4 →
      IsConj (⟨left, (sylow_quaternion_eight_involution_data sylow isomorphism).2.2 left.property⟩ :
        centralizer) ⟨right, (sylow_quaternion_eight_involution_data sylow isomorphism).2.2 right.property⟩ := by
  intro involution centralizer left right hleft hright
  obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp
    (perfect_sylow_quaternion_eight_total_four_fusion sylow isomorphism left right hleft hright)
  have hleftSquare : (left : G) ^ 2 = involution := congrArg Subtype.val
    (sylow_quaternion_eight_four_square sylow isomorphism left hleft)
  have hrightSquare : (right : G) ^ 2 = involution := congrArg Subtype.val
    (sylow_quaternion_eight_four_square sylow isomorphism right hright)
  have hfixes : conjugator * (involution : G) * conjugator⁻¹ = involution := by
    calc
      _ = (MulAut.conj conjugator) ((left : G) ^ 2) := by rw [hleftSquare]; rfl
      _ = ((MulAut.conj conjugator) (left : G)) ^ 2 := map_pow _ _ _
      _ = (right : G) ^ 2 := by rw [MulAut.conj_apply, hconjugator]
      _ = involution := hrightSquare
  have hmember : conjugator ∈ centralizer := Subgroup.mem_centralizer_singleton_iff.mpr
    ((mul_inv_eq_iff_eq_mul).mp hfixes)
  exact isConj_iff.mpr ⟨⟨conjugator, hmember⟩, Subtype.ext hconjugator⟩

theorem sylow_quaternion_eight_two_element_order {G : Type*} [Group G] [Finite G]
    (sylow : Sylow 2 G) (isomorphism : (sylow : Subgroup G) ≃* QuaternionGroup 2)
    (element : G) (horder : ∃ exponent, orderOf element = 2 ^ exponent) :
    orderOf element = 1 ∨ orderOf element = 2 ∨ orderOf element = 4 := by
  obtain ⟨member, hconj⟩ := two_element_isConj_sylow sylow element horder
  have horderEqual : orderOf element = orderOf (isomorphism member) := by
    exact (orderOf_eq_of_isConj hconj).trans
      ((Subgroup.orderOf_coe member).trans (isomorphism.orderOf_eq member).symm)
  rw [horderEqual]
  rcases quaternionEight_element_class (isomorphism member) with hone | hinvolution |
      ⟨label, hrepresentative⟩
  · left; rw [hone, orderOf_one]
  · right; left; rw [hinvolution, quaternionEight_involution_order]
  · right; right
    rcases hrepresentative with hrepresentative | hinverse
    · rw [hrepresentative, quaternionEight_representative_order]
    · rw [hinverse, orderOf_inv, quaternionEight_representative_order]

theorem sylow_quaternion_eight_global_two_classes {G : Type*}
    [Group G] [Finite G] [Group.IsPerfect G] (sylow : Sylow 2 G)
    (isomorphism : (sylow : Subgroup G) ≃* QuaternionGroup 2) :
    let involution := isomorphism.symm (QuaternionGroup.a (2 : ZMod 4))
    let generator := isomorphism.symm (QuaternionGroup.a (1 : ZMod 4))
    ∀ element : G, (∃ exponent, orderOf element = 2 ^ exponent) ↔
      element = 1 ∨ IsConj element (involution : G) ∨ IsConj element (generator : G) := by
  intro involution generator element
  have hinvolutionOrder : orderOf (involution : G) = 2 :=
    (sylow_quaternion_eight_involution_data sylow isomorphism).1
  have hgeneratorOrder : orderOf generator = 4 :=
    (isomorphism.symm.orderOf_eq _).trans QuaternionGroup.orderOf_a_one
  constructor
  · intro horder
    obtain ⟨member, hconj⟩ := two_element_isConj_sylow sylow element horder
    rcases sylow_quaternion_eight_two_element_order sylow isomorphism element horder with
      hone | htwo | hfour
    · exact Or.inl (orderOf_eq_one_iff.mp hone)
    · right; left
      have hequal : (member : G) = involution :=
        (sylow_quaternion_eight_involution_data sylow isomorphism).2.1 _ member.property
          ((orderOf_eq_of_isConj hconj).symm.trans htwo)
      rwa [hequal] at hconj
    · right; right
      exact hconj.trans (perfect_sylow_quaternion_eight_total_four_fusion sylow isomorphism
        member generator ((Subgroup.orderOf_coe member).symm.trans
          ((orderOf_eq_of_isConj hconj).symm.trans hfour)) hgeneratorOrder)
  · intro hclasses
    rcases hclasses with hone | htwo | hfour
    · exact ⟨0, by rw [hone, orderOf_one, pow_zero]⟩
    · exact ⟨1, by rw [orderOf_eq_of_isConj htwo, hinvolutionOrder, pow_one]⟩
    · exact ⟨2, by rw [orderOf_eq_of_isConj hfour, Subgroup.orderOf_coe, hgeneratorOrder]; norm_num⟩

theorem sylow_quaternion_eight_centralizer_two_classes {G : Type*}
    [Group G] [Finite G] [Group.IsPerfect G] (sylow : Sylow 2 G)
    (isomorphism : (sylow : Subgroup G) ≃* QuaternionGroup 2) :
    let involution := isomorphism.symm (QuaternionGroup.a (2 : ZMod 4))
    let centralizer := Subgroup.centralizer ({(involution : G)} : Set G)
    let hle := (sylow_quaternion_eight_involution_data sylow isomorphism).2.2
    let localInvolution : centralizer := ⟨involution, hle involution.property⟩
    let generator := isomorphism.symm (QuaternionGroup.a (1 : ZMod 4))
    let localGenerator : centralizer := ⟨generator, hle generator.property⟩
    ∀ element : centralizer, (∃ exponent, orderOf element = 2 ^ exponent) ↔
      element = 1 ∨ element = localInvolution ∨ IsConj element localGenerator := by
  intro involution centralizer hle localInvolution generator localGenerator element
  have hinvolutionOrder : orderOf localInvolution = 2 :=
    (Subgroup.orderOf_coe localInvolution).symm.trans
      (sylow_quaternion_eight_involution_data sylow isomorphism).1
  have hgeneratorOrder : orderOf generator = 4 :=
    (isomorphism.symm.orderOf_eq _).trans QuaternionGroup.orderOf_a_one
  have hlocalGeneratorOrder : orderOf localGenerator = 4 :=
    (Subgroup.orderOf_coe localGenerator).symm.trans
      ((Subgroup.orderOf_coe generator).trans hgeneratorOrder)
  constructor
  · intro horder
    let localSylow := sylow.subtype hle
    obtain ⟨member, hconj⟩ := two_element_isConj_sylow localSylow element horder
    have hmemberOriginal : ((member : centralizer) : G) ∈ (sylow : Subgroup G) := by
      have hmember := member.property
      simpa only [localSylow, Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hmember
    let originalMember : (sylow : Subgroup G) := ⟨(member : centralizer), hmemberOriginal⟩
    have hambientOrder : ∃ exponent, orderOf (element : G) = 2 ^ exponent := by
      simpa only [Subgroup.orderOf_coe] using horder
    rcases sylow_quaternion_eight_two_element_order sylow isomorphism element hambientOrder with
      hone | htwo | hfour
    · left
      exact Subtype.ext (orderOf_eq_one_iff.mp hone)
    · right; left
      exact Subtype.ext (sylow_quaternion_eight_centralizer_unique_involution sylow isomorphism
        element element.property htwo)
    · right; right
      have horiginalOrder : orderOf originalMember = 4 := by
        rw [← Subgroup.orderOf_coe originalMember]
        change orderOf ((member : centralizer) : G) = 4
        rw [Subgroup.orderOf_coe, ← orderOf_eq_of_isConj hconj, ← Subgroup.orderOf_coe element]
        exact hfour
      exact hconj.trans (sylow_quaternion_eight_centralizer_four_fusion sylow isomorphism
        originalMember generator horiginalOrder hgeneratorOrder)
  · intro hclasses
    rcases hclasses with hone | htwo | hfour
    · exact ⟨0, by rw [hone, orderOf_one, pow_zero]⟩
    · exact ⟨1, by rw [htwo, hinvolutionOrder, pow_one]⟩
    · exact ⟨2, by rw [orderOf_eq_of_isConj hfour, hlocalGeneratorOrder]; norm_num⟩

end CFSG.TwoRankLowerBound.Helpers
