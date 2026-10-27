module

public import CFSG.LocalAnalysis.ComponentClassification.OddKernelNormalizers

public section

namespace CFSG.ComponentClassification.OddKernelInvolutions

theorem cyclic_mem_cases {G : Type*} [Group G] (element : G) (horder : orderOf element = 2)
    (member : G) (hmember : member ∈ Subgroup.zpowers element) : member = 1 ∨ member = element := by
  obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmember
  have hmod := zpow_mod_orderOf element exponent
  rw [horder] at hmod
  change element ^ (exponent % 2) = element ^ exponent at hmod
  have hcases : exponent % 2 = 0 ∨ exponent % 2 = 1 := by omega
  rcases hcases with hzero | hone
  · left
    rw [← hmod, hzero, zpow_zero]
  · right
    rw [← hmod, hone, zpow_one]

theorem normalizer_cyclic_eq_centralizer {G : Type*} [Group G]
    (element : G) (horder : orderOf element = 2) :
    Subgroup.normalizer (Subgroup.zpowers element : Set G) =
      Subgroup.centralizer ({element} : Set G) := by
  apply le_antisymm
  · intro member hmember
    have hconjugate := (Subgroup.mem_normalizer_iff.mp hmember element).mp
      (Subgroup.mem_zpowers element)
    rcases cyclic_mem_cases element horder _ hconjugate with hone | heq
    · have helement : element = 1 := by
        have hvalue := congrArg (fun value : G => member⁻¹ * value * member) hone
        simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, mul_one,
          inv_mul_cancel] using hvalue
      rw [helement, orderOf_one] at horder
      omega
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      calc
        member * element = (member * element * member⁻¹) * member := by group
        _ = element * member := by rw [heq]
  · intro member hmember
    apply Subgroup.mem_normalizer_iff.mpr
    intro cyclicMember
    have hcommutes := Subgroup.mem_centralizer_singleton_iff.mp hmember
    constructor
    · intro hcyclic
      rcases cyclic_mem_cases element horder cyclicMember hcyclic with hone | helement
      · rw [hone]
        simp
      · rw [helement]
        have heq : member * element * member⁻¹ = element := by rw [hcommutes]; group
        rw [heq]
        exact Subgroup.mem_zpowers element
    · intro hconjugate
      rcases cyclic_mem_cases element horder _ hconjugate with hone | heq
      · have hcyclicOne : cyclicMember = 1 := by
          have hvalue := congrArg (fun value : G => member⁻¹ * value * member) hone
          simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, mul_one,
            inv_mul_cancel] using hvalue
        rw [hcyclicOne]
        exact Subgroup.one_mem _
      · have hcyclicElement : cyclicMember = element := by
          have hvalue := congrArg (fun value : G => member⁻¹ * value * member) heq
          have hconjugateFixed : member⁻¹ * element * member = element := by
            calc
              member⁻¹ * element * member = member⁻¹ * (element * member) := by group
              _ = member⁻¹ * (member * element) := by rw [hcommutes]
              _ = element := by group
          calc
            cyclicMember = member⁻¹ * (member * cyclicMember * member⁻¹) * member := by group
            _ = member⁻¹ * element * member := hvalue
            _ = element := hconjugateFixed
        rw [hcyclicElement]
        exact Subgroup.mem_zpowers element

theorem image_order {G H : Type*} [Group G] [Finite G] [Group H]
    (quotient : G →* H) (hodd : Odd (Nat.card quotient.ker))
    (element : G) (horder : orderOf element = 2) : orderOf (quotient element) = 2 := by
  have hcyclic : IsPGroup 2 (Subgroup.zpowers element) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, horder]; rfl)
  have hinjective := OddKernel.image_injective_on_two quotient hodd (Subgroup.zpowers element) hcyclic
  have hmap := orderOf_injective (quotient.domRestrict (Subgroup.zpowers element)) hinjective
    (⟨element, Subgroup.mem_zpowers element⟩ : Subgroup.zpowers element)
  have hinclusion := orderOf_injective (Subgroup.zpowers element).subtype
    (Subgroup.zpowers element).subtype_injective (⟨element, Subgroup.mem_zpowers element⟩ : Subgroup.zpowers element)
  exact hmap.trans (hinclusion.symm.trans horder)

theorem image_centralizer {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hodd : Odd (Nat.card quotient.ker)) (element : G) (horder : orderOf element = 2) :
    (Subgroup.centralizer ({element} : Set G)).map quotient =
      Subgroup.centralizer ({quotient element} : Set H) := by
  have hcyclic : IsPGroup 2 (Subgroup.zpowers element) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, horder]; rfl)
  have hcyclicImage : (Subgroup.zpowers element).map quotient = Subgroup.zpowers (quotient element) := by
    apply le_antisymm
    · rintro member ⟨lift, hlift, rfl⟩
      obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hlift
      rw [map_zpow]
      exact Subgroup.zpow_mem_zpowers _ _
    · apply Subgroup.zpowers_le.mpr
      exact Subgroup.mem_map_of_mem quotient (Subgroup.mem_zpowers element)
  have hnormalizer := OddKernelNormalizers.image quotient hsurjective hodd
    (Subgroup.zpowers element) hcyclic
  rw [normalizer_cyclic_eq_centralizer element horder, hcyclicImage,
    normalizer_cyclic_eq_centralizer (quotient element) (image_order quotient hodd element horder)]
    at hnormalizer
  exact hnormalizer

theorem component_image {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hodd : Odd (Nat.card quotient.ker)) [Group.IsSolvable quotient.ker]
    (element : G) (horder : orderOf element = 2)
    (component : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hcomponent : CFSG.Open.IsComponentOf component ⊤) :
    CFSG.Open.IsComponentOf
      (((component.map (Subgroup.centralizer ({element} : Set G)).subtype).map quotient).subgroupOf
        (Subgroup.centralizer ({quotient element} : Set H))) ⊤ := by
  let domain := Subgroup.centralizer ({element} : Set G)
  let codomain := Subgroup.centralizer ({quotient element} : Set H)
  have himage : domain.map quotient = codomain :=
    image_centralizer quotient hsurjective hodd element horder
  let restriction : domain →* codomain :=
    (quotient.domRestrict domain).codRestrict codomain
      (fun member => himage ▸ Subgroup.mem_map_of_mem quotient member.property)
  have hrestriction : Function.Surjective restriction := by
    intro member
    have hmem : member.val ∈ domain.map quotient := by
      rw [himage]
      exact member.property
    obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨lift, hlift⟩, Subtype.ext heq⟩
  let kernelEmbedding : restriction.ker →* quotient.ker :=
    { toFun := fun member => ⟨member.val.val,
        congrArg Subtype.val (MonoidHom.mem_ker.mp member.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hkernelEmbedding : Function.Injective kernelEmbedding := by
    intro left right heq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun member : quotient.ker => member.val) heq
  let : Group.IsSolvable restriction.ker :=
    Group.isSolvable_of_isSolvable_injective hkernelEmbedding
  have hnotKilled : ¬ component ≤ restriction.ker := by
    intro hle
    let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
    let : Nontrivial component := Quasisimple.nontrivial hcomponent.2.2
    let : Group.IsSolvable component :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable component inferInstance
  have hlocal := LocalComponents.image hcomponent restriction hrestriction hnotKilled
  have hmap : component.map restriction =
      (((component.map domain.subtype).map quotient).subgroupOf codomain) := by
    ext member
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact Subgroup.mem_map.mpr ⟨lift.val, Subgroup.mem_map_of_mem domain.subtype hlift, rfl⟩
    · intro hmember
      obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp hmember
      obtain ⟨original, horiginal, rfl⟩ := Subgroup.mem_map.mp hlift
      exact Subgroup.mem_map.mpr ⟨original, horiginal, Subtype.ext heq⟩
  rwa [hmap] at hlocal

theorem twoComponent_quasisimple_image {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hodd : Odd (Nat.card quotient.ker)) (element : G) (horder : orderOf element = 2)
    (component : Subgroup G)
    (hcentralizes : component ≤ Subgroup.centralizer ({element} : Set G))
    (hcomponent : CFSG.ComponentClassification.TwoComponents.IsTwoComponent
      (component.subgroupOf (Subgroup.centralizer ({element} : Set G))))
    (hquasisimple : CFSG.Open.IsQuasisimple (component.map quotient)) :
    CFSG.Open.IsComponentOf
      ((component.map quotient).subgroupOf (Subgroup.centralizer ({quotient element} : Set H))) ⊤ := by
  let domain := Subgroup.centralizer ({element} : Set G)
  let codomain := Subgroup.centralizer ({quotient element} : Set H)
  have himage : domain.map quotient = codomain :=
    image_centralizer quotient hsurjective hodd element horder
  let restriction : domain →* codomain :=
    (quotient.domRestrict domain).codRestrict codomain
      (fun member => himage ▸ Subgroup.mem_map_of_mem quotient member.property)
  have hrestriction : Function.Surjective restriction := by
    intro member
    have hmem : member.val ∈ domain.map quotient := by rw [himage]; exact member.property
    obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨lift, hlift⟩, Subtype.ext heq⟩
  have hkernel : restriction.ker = (quotient.domRestrict domain).ker := by
    ext member
    change restriction member = 1 ↔ quotient member.val = 1
    exact ⟨fun heq => congrArg Subtype.val heq, fun heq => Subtype.ext heq⟩
  have hrestrictionOdd : Odd (Nat.card restriction.ker) := by
    rw [hkernel]
    exact OddKernel.odd_card_restriction_kernel quotient hodd domain
  have htwoImage := OddKernelTwoComponents.image restriction hrestriction hrestrictionOdd
    (component.subgroupOf domain) hcomponent
  have himageLe : component.map quotient ≤ codomain := by
    rintro member ⟨lift, hlift, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg quotient
      (Subgroup.mem_centralizer_singleton_iff.mp (hcentralizes hlift))
  have hmap : (component.subgroupOf domain).map restriction =
      (component.map quotient).subgroupOf codomain := by
    ext member
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact Subgroup.mem_map.mpr ⟨lift.val, hlift, rfl⟩
    · intro hmember
      obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp hmember
      exact Subgroup.mem_map.mpr ⟨⟨lift, hcentralizes hlift⟩, hlift, Subtype.ext heq⟩
  rw [hmap] at htwoImage
  exact ⟨le_top, htwoImage.1, Components.quasisimple_of_equiv
    (Subgroup.subgroupOfEquivOfLe himageLe) hquasisimple⟩

end CFSG.ComponentClassification.OddKernelInvolutions
