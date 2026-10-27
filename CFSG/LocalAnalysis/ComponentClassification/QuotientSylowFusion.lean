module

public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProduct
public import CFSG.LocalAnalysis.ComponentClassification.TwoSubgroupSylowConjugacy

public section

namespace CFSG.ComponentClassification.QuotientSylowFusion

theorem correction {G H : Type*} [Group G] [Finite G] [Group H]
    (homomorphism : G →* H) (sylow : Sylow 2 G) (member actor : G)
    (horder : orderOf member = 2)
    (hfused : homomorphism (actor * member * actor⁻¹) ∈ (sylow : Subgroup G).map homomorphism) :
    ∃ correction ∈ homomorphism.ker,
      correction * (actor * member * actor⁻¹) * correction⁻¹ ∈ (sylow : Subgroup G) := by
  let fused := actor * member * actor⁻¹
  let overgroup := (sylow : Subgroup G) ⊔ homomorphism.ker
  have hfusedOvergroup : fused ∈ overgroup := by
    have hpreimage : fused ∈ ((sylow : Subgroup G).map homomorphism).comap homomorphism := hfused
    rwa [Subgroup.comap_map_eq] at hpreimage
  have hfusedOrder : orderOf fused = 2 :=
    (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective member).trans horder
  have htwo : IsPGroup 2 (Subgroup.zpowers fused) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hfusedOrder]; rfl : Nat.card (Subgroup.zpowers fused) = 2 ^ 1)
  let restricted := sylow.subtype (le_sup_left : (sylow : Subgroup G) ≤ overgroup)
  obtain ⟨conjugator, hconjugator, hcontained⟩ := TwoSubgroupSylowConjugacy.into overgroup (Subgroup.zpowers fused)
    htwo (Subgroup.zpowers_le.mpr hfusedOvergroup) restricted
  have hrestricted : (restricted : Subgroup overgroup).map overgroup.subtype = (sylow : Subgroup G) := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le le_sup_left]
  rw [hrestricted] at hcontained
  have hconjugate : conjugator * fused * conjugator⁻¹ ∈ (sylow : Subgroup G) :=
    hcontained (Subgroup.mem_map.mpr ⟨fused, Subgroup.mem_zpowers fused, rfl⟩)
  have hkernelNormalizes : (sylow : Subgroup G) ≤ Subgroup.normalizer (homomorphism.ker : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨kernelMember, hkernelMember, sylowMember, hsylowMember, hproduct⟩ :=
    NormalizedProduct.coordinates homomorphism.ker (sylow : Subgroup G) hkernelNormalizes conjugator
      (by change conjugator ∈ (sylow : Subgroup G) ⊔ homomorphism.ker at hconjugator; rwa [sup_comm] at hconjugator)
  let correction := sylowMember⁻¹ * kernelMember * sylowMember
  have hcorrection : correction ∈ homomorphism.ker := by
    have hnormal : homomorphism.ker.Normal := inferInstance
    simpa only [inv_inv] using hnormal.conj_mem kernelMember hkernelMember sylowMember⁻¹
  refine ⟨correction, hcorrection, ?_⟩
  have hremoved : sylowMember⁻¹ * (conjugator * fused * conjugator⁻¹) * sylowMember ∈ (sylow : Subgroup G) :=
    (sylow : Subgroup G).mul_mem
      ((sylow : Subgroup G).mul_mem ((sylow : Subgroup G).inv_mem hsylowMember) hconjugate) hsylowMember
  rw [← hproduct] at hremoved
  convert hremoved using 1
  dsimp [correction, fused]
  group

theorem conjugate_coordinate {G : Type*} [Group G]
    (ambient : Subgroup G) [ambient.Normal] (member : G)
    (hproduct : ambient ⊔ Subgroup.zpowers member = ⊤) (actor : G) :
    (actor * member * actor⁻¹) * member⁻¹ ∈ ambient := by
  have hnormalizes : Subgroup.zpowers member ≤ Subgroup.normalizer (ambient : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨left, hleft, right, hright, heq⟩ := NormalizedProduct.coordinates ambient (Subgroup.zpowers member)
    hnormalizes actor (by rw [hproduct]; exact Subgroup.mem_top _)
  have hcommutes : right * member = member * right := by
    obtain ⟨power, rfl⟩ := Subgroup.mem_zpowers_iff.mp hright
    exact (Commute.refl member).zpow_left power
  have hnormal : ambient.Normal := inferInstance
  have hconjugate : member * left⁻¹ * member⁻¹ ∈ ambient := hnormal.conj_mem left⁻¹ (ambient.inv_mem hleft) member
  have hbound := ambient.mul_mem hleft hconjugate
  rw [← heq]
  convert hbound using 1
  calc
    _ = left * (right * member * right⁻¹) * left⁻¹ * member⁻¹ := by group
    _ = left * (member * left⁻¹ * member⁻¹) := by rw [hcommutes]; group

theorem isolated {G : Type*} [Group G] [Finite G]
    (ambient : Subgroup G) [ambient.Normal] (kernel : Subgroup G) [kernel.Normal]
    (member : G) (horder : orderOf member = 2)
    (hproduct : ambient ⊔ Subgroup.zpowers member = ⊤) (hdisjoint : Disjoint ambient (Subgroup.zpowers member))
    (fixed : Subgroup G) (hfixed : fixed ≤ ambient)
    (hcentralizes : member ∈ Subgroup.centralizer (fixed : Set G))
    (hsquares : ∀ element ∈ fixed, element ^ 2 = 1 → element ∈ kernel)
    (sylow : Sylow 2 G) (hsylow : (sylow : Subgroup G) = fixed ⊔ Subgroup.zpowers member) :
    ∀ actor : G ⧸ kernel,
      actor * (QuotientGroup.mk' kernel) member * actor⁻¹ ∈
        (sylow : Subgroup G).map (QuotientGroup.mk' kernel) →
      actor * (QuotientGroup.mk' kernel) member * actor⁻¹ = (QuotientGroup.mk' kernel) member := by
  let quotient := QuotientGroup.mk' kernel
  intro actor hfused
  obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective kernel actor
  have hfusedLift : quotient (lift * member * lift⁻¹) ∈ (sylow : Subgroup G).map quotient := by
    simpa only [map_mul, map_inv] using hfused
  obtain ⟨correction, hcorrection, hcorrected⟩ := correction quotient sylow member lift horder hfusedLift
  have hcorrectionKernel : correction ∈ kernel := by
    change correction ∈ (QuotientGroup.mk' kernel).ker at hcorrection
    rwa [QuotientGroup.ker_mk'] at hcorrection
  let corrected := correction * (lift * member * lift⁻¹) * correction⁻¹
  have hcorrectedCoordinate : corrected * member⁻¹ ∈ ambient := by
    convert conjugate_coordinate ambient member hproduct (correction * lift) using 1
    dsimp [corrected]
    group
  have hcyclicNormalizes : Subgroup.zpowers member ≤ Subgroup.normalizer (fixed : Set G) :=
    Subgroup.zpowers_le.mpr ((Subgroup.centralizer_le_normalizer _) hcentralizes)
  obtain ⟨left, hleft, right, hright, hcoordinates⟩ := NormalizedProduct.coordinates fixed (Subgroup.zpowers member)
    hcyclicNormalizes corrected (by rw [← hsylow]; exact hcorrected)
  have hrightAmbient : right * member⁻¹ ∈ ambient := by
    have hbound := ambient.mul_mem (ambient.inv_mem (hfixed hleft)) hcorrectedCoordinate
    rw [← hcoordinates] at hbound
    simpa only [mul_assoc, inv_mul_cancel_left] using hbound
  have hrightCyclic : right * member⁻¹ ∈ Subgroup.zpowers member :=
    (Subgroup.zpowers member).mul_mem hright ((Subgroup.zpowers member).inv_mem (Subgroup.mem_zpowers member))
  have hrightEq : right = member := mul_inv_eq_one.mp
    (Subgroup.mem_bot.mp (hdisjoint.eq_bot ▸ (show right * member⁻¹ ∈ ambient ⊓ Subgroup.zpowers member from
      ⟨hrightAmbient, hrightCyclic⟩)))
  rw [hrightEq] at hcoordinates
  have hcorrectedSquare : corrected ^ 2 = 1 := by
    have hconjugateOrder := orderOf_injective (MulAut.conj (correction * lift)).toMonoidHom
      (MulAut.conj (correction * lift)).injective member
    have hcorrectedOrder : orderOf corrected = 2 := by
      convert hconjugateOrder.trans horder using 1
      dsimp [corrected]
      congr 1
      group
    exact orderOf_dvd_iff_pow_eq_one.mp (hcorrectedOrder ▸ dvd_rfl)
  have hleftSquare : left ^ 2 = 1 := by
    have hcommutes := (Subgroup.mem_centralizer_iff.mp hcentralizes left hleft)
    have hmemberSquare : member ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (horder ▸ dvd_rfl)
    rw [← hcoordinates, pow_two] at hcorrectedSquare
    have hproductSquare : left * member * (left * member) = left ^ 2 := by
      calc
        _ = left * (member * left) * member := by group
        _ = left * (left * member) * member := by rw [← hcommutes]
        _ = left ^ 2 * member ^ 2 := by simp only [pow_two]; group
        _ = left ^ 2 := by rw [hmemberSquare, mul_one]
    rwa [hproductSquare] at hcorrectedSquare
  have hleftOne : quotient left = 1 := (QuotientGroup.eq_one_iff _).mpr (hsquares left hleft hleftSquare)
  have hcorrectionOne : quotient correction = 1 := (QuotientGroup.eq_one_iff _).mpr hcorrectionKernel
  have hcorrectedImage : quotient corrected = quotient member := by
    rw [← hcoordinates, map_mul, hleftOne, one_mul]
  have hfusedImage : quotient corrected = quotient lift * quotient member * (quotient lift)⁻¹ := by
    dsimp [corrected]
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hcorrectionOne, one_mul, inv_one, mul_one]
  exact hfusedImage.symm.trans hcorrectedImage

end CFSG.ComponentClassification.QuotientSylowFusion
