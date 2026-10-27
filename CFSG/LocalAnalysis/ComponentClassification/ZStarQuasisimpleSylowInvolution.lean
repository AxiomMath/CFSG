module

public import CFSG.LocalAnalysis.ComponentClassification.TwoActionZStarEscape
public import CFSG.LocalAnalysis.ComponentClassification.NormalCenterQuotientImage
public import CFSG.LocalAnalysis.ComponentClassification.QuotientSylowFusion

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ZStarQuasisimpleSylowInvolution

theorem centralizes_quotient {G : Type*} [Group G] [Finite G]
    (ambient kernel : Subgroup G) [ambient.Normal] [kernel.Normal]
    (hquasisimple : IsQuasisimple ambient) (heven : Even (Nat.card ambient))
    (hkernelLe : kernel ≤ ambient)
    (hkernel : kernel.subgroupOf ambient = Subgroup.center ambient)
    (member : G) (horder : orderOf member = 2)
    (hproduct : ambient ⊔ Subgroup.zpowers member = ⊤)
    (hdisjoint : Disjoint ambient (Subgroup.zpowers member))
    (fixed : Sylow 2 ambient)
    (hcentralizes : member ∈ Subgroup.centralizer
      (((fixed : Subgroup ambient).map ambient.subtype : Subgroup G) : Set G))
    (hsquares : ∀ element ∈ (fixed : Subgroup ambient).map ambient.subtype,
      element ^ 2 = 1 → element ∈ kernel) :
    ∀ element : G, (QuotientGroup.mk' kernel) element * (QuotientGroup.mk' kernel) member =
      (QuotientGroup.mk' kernel) member * (QuotientGroup.mk' kernel) element := by
  let cyclic := Subgroup.zpowers member
  let fixedImage := (fixed : Subgroup ambient).map ambient.subtype
  let quotient := QuotientGroup.mk' kernel
  have hfixed : fixedImage ≤ ambient := by
    rintro element ⟨lift, hlift, rfl⟩
    exact lift.property
  have htwo : IsPGroup 2 cyclic := IsPGroup.of_card
    (by rw [Nat.card_zpowers, horder]; rfl : Nat.card cyclic = 2 ^ 1)
  have hnormalizes : cyclic ≤ Subgroup.normalizer (ambient : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hnormalizesFixed : cyclic ≤ Subgroup.normalizer (fixedImage : Set G) :=
    Subgroup.zpowers_le.mpr ((Subgroup.centralizer_le_normalizer _) hcentralizes)
  let productSylow := NormalizedProductSylow.sylow ambient cyclic htwo hnormalizes fixed hnormalizesFixed
  let equivalence := (MulEquiv.subgroupCongr hproduct).trans Subgroup.topEquiv
  let sylow := productSylow.mapSurjective (f := equivalence.toMonoidHom)
    (show Function.Surjective equivalence.toMonoidHom from equivalence.surjective)
  have hsylow : (sylow : Subgroup G) = fixedImage ⊔ cyclic := by
    rw [Sylow.coe_mapSurjective, NormalizedProductSylow.coe_sylow]
    have hmap := Subgroup.map_subgroupOf_eq_of_le
      (show fixedImage ⊔ cyclic ≤ ambient ⊔ cyclic from sup_le (hfixed.trans le_sup_left) le_sup_right)
    convert hmap using 1
    have heq : equivalence.toMonoidHom = (ambient ⊔ cyclic).subtype := by
      ext element
      rfl
    rw [heq]
  let quotientSylow := sylow.mapSurjective (f := quotient) (QuotientGroup.mk'_surjective kernel)
  have hquotientSylow : (quotientSylow : Subgroup (G ⧸ kernel)) = (sylow : Subgroup G).map quotient :=
    Sylow.coe_mapSurjective _ _
  have hmemberSylow : member ∈ (sylow : Subgroup G) := by
    rw [hsylow]
    exact (le_sup_right : cyclic ≤ fixedImage ⊔ cyclic) (Subgroup.mem_zpowers member)
  have hquotientOrder : orderOf (quotient member) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      rw [orderOf_dvd_iff_pow_eq_one.mp (horder ▸ dvd_rfl), map_one]
    · intro hone
      have hmemberKernel := (QuotientGroup.eq_one_iff member).mp hone
      have hmemberAmbient : member ∈ ambient := hkernelLe hmemberKernel
      have hmemberOne := Subgroup.mem_bot.mp (hdisjoint.eq_bot ▸
        (show member ∈ ambient ⊓ cyclic from ⟨hmemberAmbient, Subgroup.mem_zpowers member⟩))
      rw [hmemberOne, orderOf_one] at horder
      omega
  have hcentral : member ∈ Subgroup.centralizer (sylow : Set G) := by
    change member ∈ Subgroup.centralizer ((sylow : Subgroup G) : Set G)
    rw [hsylow]
    apply Subgroup.mem_centralizer_iff.mpr
    intro element helement
    have hfixedCentral : fixedImage ≤ Subgroup.centralizer {member} := by
      intro central hcentral
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hcentralizes central hcentral)
    have hcyclicCentral : cyclic ≤ Subgroup.centralizer {member} := by
      apply Subgroup.zpowers_le.mpr
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    exact Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hfixedCentral hcyclicCentral) helement)
  have hcenter : quotient member ∈ (Subgroup.center (quotientSylow : Subgroup (G ⧸ kernel))).map
      (quotientSylow : Subgroup (G ⧸ kernel)).subtype := by
    have hmemberImage : quotient member ∈ (quotientSylow : Subgroup (G ⧸ kernel)) := by
      rw [hquotientSylow]
      exact Subgroup.mem_map.mpr ⟨member, hmemberSylow, rfl⟩
    apply Subgroup.mem_map.mpr
    refine ⟨⟨quotient member, hmemberImage⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro other
    apply Subtype.ext
    have hother := other.property
    simp only [hquotientSylow] at hother
    obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp hother
    change other.val * quotient member = quotient member * other.val
    rw [← heq]
    rw [← map_mul, ← map_mul]
    exact congrArg quotient (Subgroup.mem_centralizer_iff.mp hcentral lift hlift)
  have hisolated := QuotientSylowFusion.isolated ambient kernel member horder hproduct hdisjoint fixedImage hfixed
    hcentralizes hsquares sylow hsylow
  have htwoQuotient : IsPGroup 2 (G ⧸ ambient) := by
    have hnormal : cyclic ≤ Subgroup.normalizer (ambient : Set G) := hnormalizes
    have htwoProduct := TwoProductOddCore.quotient_two ambient cyclic hnormal htwo
    have hsurjective : Function.Surjective ((QuotientGroup.mk' ambient).comp equivalence.toMonoidHom) :=
      (QuotientGroup.mk'_surjective ambient).comp equivalence.surjective
    have hkernelBound : ambient.subgroupOf (ambient ⊔ cyclic) ≤
        ((QuotientGroup.mk' ambient).comp equivalence.toMonoidHom).ker := by
      intro element helement
      exact (QuotientGroup.eq_one_iff element.val).mpr helement
    let induced := QuotientGroup.lift (ambient.subgroupOf (ambient ⊔ cyclic))
      ((QuotientGroup.mk' ambient).comp equivalence.toMonoidHom) hkernelBound
    have hinducedSurjective : Function.Surjective induced := by
      intro element
      obtain ⟨lift, hlift⟩ := hsurjective element
      refine ⟨(QuotientGroup.mk' (ambient.subgroupOf (ambient ⊔ cyclic))) lift, ?_⟩
      exact (congrArg (fun hom : ↥(ambient ⊔ cyclic) →* (G ⧸ ambient) => hom lift)
        (QuotientGroup.lift_comp_mk' _ _ hkernelBound)).trans hlift
    exact htwoProduct.of_surjective induced hinducedSurjective
  have hcore := NormalCenterQuotientImage.odd_core_trivial ambient kernel hquasisimple heven hkernel htwoQuotient
  have htop := (TwoActionZStarEscape.twoActionZStar (G := G ⧸ kernel))
    quotientSylow (quotient member) hquotientOrder hcenter (by
    intro actor hactor
    apply hisolated actor
    rwa [← hquotientSylow])
  rw [hcore, sup_bot_eq] at htop
  intro element
  have hmember : quotient element ∈ Subgroup.centralizer {quotient member} := by
    rw [htop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_centralizer_singleton_iff.mp hmember

theorem centralizes_ambient {G : Type*} [Group G]
    (ambient kernel : Subgroup G) [ambient.Normal] [kernel.Normal]
    (hperfect : commutator ambient = ⊤)
    (hkernel : kernel.subgroupOf ambient = Subgroup.center ambient)
    (member : G)
    (hquotientCentral : ∀ element : G, (QuotientGroup.mk' kernel) element * (QuotientGroup.mk' kernel) member =
      (QuotientGroup.mk' kernel) member * (QuotientGroup.mk' kernel) element) :
    member ∈ Subgroup.centralizer (ambient : Set G) := by
  let : Group.IsPerfect ambient := ⟨hperfect⟩
  have hnormalizes : member ∈ Subgroup.normalizer (ambient : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  let automorphism := ambient.normalizerMonoidHom ⟨member, hnormalizes⟩
  have hcentral : ∀ element : ambient, element⁻¹ * automorphism element ∈ Subgroup.center ambient := by
    intro element
    rw [← hkernel]
    change element.val⁻¹ * (member * element.val * member⁻¹) ∈ kernel
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' kernel) (element.val⁻¹ * (member * element.val * member⁻¹)) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hquotientCentral element.val]
    group
  have hidentity := PerfectAutomorphisms.hom_eq_id_of_central_displacement automorphism.toMonoidHom hcentral
  apply Subgroup.mem_centralizer_iff.mpr
  intro element helement
  have heq := congrArg (fun hom : ambient →* ambient => hom (⟨element, helement⟩ : ambient)) hidentity
  have heqAmbient := congrArg Subtype.val heq
  change member * element * member⁻¹ = element at heqAmbient
  exact (mul_inv_eq_iff_eq_mul.mp heqAmbient).symm

end CFSG.ComponentClassification.ZStarQuasisimpleSylowInvolution
