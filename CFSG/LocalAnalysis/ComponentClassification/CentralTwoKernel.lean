module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.Open.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.ComponentClassification.Components
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.ComponentClassification.Layer
public import CFSG.LocalAnalysis.ComponentClassification.TwoResidual
public import CFSG.LocalAnalysis.ComponentClassification.OddKernel
public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions

public section

open CFSG.Open

namespace CFSG.ComponentClassification.CentralTwoKernel

theorem restriction_kernel_two {G H : Type*} [Group G] [Group H]
    (quotient : G →* H) (htwoKernel : IsPGroup 2 quotient.ker) (subgroup : Subgroup G) :
    IsPGroup 2 (quotient.domRestrict subgroup).ker := by
  let inclusion : (quotient.domRestrict subgroup).ker →* quotient.ker :=
    { toFun := fun element => ⟨element.val.val, element.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply htwoKernel.of_injective inclusion
  intro left right heq
  have hvalue : left.val.val = right.val.val := congrArg (fun element : quotient.ker => element.val) heq
  exact Subtype.ext (Subtype.ext hvalue)

theorem restriction_kernel_central {G H : Type*} [Group G] [Group H]
    (quotient : G →* H) (hcentralKernel : quotient.ker ≤ Subgroup.center G)
    (subgroup : Subgroup G) :
    (quotient.domRestrict subgroup).ker ≤ Subgroup.center subgroup := by
  intro element hmem
  apply Subgroup.mem_center_iff.mpr
  intro other
  exact Subtype.ext ((Subgroup.mem_center_iff.mp (hcentralKernel hmem)) other.val)

theorem core_image {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) (htwoKernel : IsPGroup 2 quotient.ker) :
    (componentClassificationOddCore G).map quotient = componentClassificationOddCore H := by
  apply le_antisymm (OddKernel.core_map_le quotient hsurjective)
  let preimage := (componentClassificationOddCore H).comap quotient
  let : preimage.Normal := Subgroup.Normal.comap inferInstance quotient
  let restriction : preimage →* componentClassificationOddCore H :=
    (quotient.domRestrict preimage).codRestrict _ fun element => element.property
  have hrestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hlift⟩ := hsurjective element.val
    have hmem : lift ∈ preimage := by
      change quotient lift ∈ componentClassificationOddCore H
      rw [hlift]
      exact element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hlift⟩
  have hkernel : restriction.ker = quotient.ker.subgroupOf preimage := by
    ext element
    change restriction element = 1 ↔ quotient element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hkernelTwo : IsPGroup 2 restriction.ker := by
    rw [hkernel]
    exact htwoKernel.of_equiv
      (Subgroup.subgroupOfEquivOfLe (Subgroup.ker_le_comap quotient _)).symm
  have hoddIndex : Odd restriction.ker.index := by
    have hindex : restriction.ker.index = Nat.card (componentClassificationOddCore H) := by
      rw [Subgroup.index_eq_card,
        Nat.card_congr (QuotientGroup.liftEquiv restriction.ker hrestriction rfl).toEquiv]
    rw [hindex]
    exact OddCore.odd_card H
  let sylow : Sylow 2 preimage := hkernelTwo.toSylow hoddIndex.not_two_dvd_nat
  have hsylow : (sylow : Subgroup preimage) = restriction.ker := hkernelTwo.toSylow_coe _
  have hsylowCentral : (sylow : Subgroup preimage) ≤ Subgroup.center preimage := by
    rw [hsylow]
    intro element hmem
    have hone : restriction element = 1 := MonoidHom.mem_ker.mp hmem
    have hcentral : element.val ∈ Subgroup.center G :=
      hcentralKernel (congrArg Subtype.val hone)
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hcentral) other.val)
  have hnormalizer : Subgroup.normalizer (sylow : Set preimage) ≤
      Subgroup.centralizer (sylow : Set preimage) := by
    intro element _
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    exact ((Subgroup.mem_center_iff.mp (hsylowCentral hmember)) element).symm
  let transfer := MonoidHom.transferSylow sylow hnormalizer
  have hcomplement : transfer.ker ⊔ (sylow : Subgroup preimage) = ⊤ :=
    (MonoidHom.ker_transferSylow_isComplement' sylow hnormalizer).sup_eq_top
  have hoddComplement : Odd (Nat.card transfer.ker) := Nat.coprime_two_left.mp
    (Nat.prime_two.coprime_iff_not_dvd.mpr
      (MonoidHom.not_dvd_card_ker_transferSylow sylow hnormalizer))
  have hlocalCoreLe : transfer.ker ≤ componentClassificationOddCore preimage :=
    OddCore.maximal preimage _ inferInstance hoddComplement
  have hambientCoreLe : transfer.ker.map preimage.subtype ≤ componentClassificationOddCore G := by
    have hmap := Subgroup.map_mono (f := preimage.subtype) hlocalCoreLe
    rw [OddCore.normal_intersection G preimage] at hmap
    exact hmap.trans inf_le_right
  intro element hmem
  obtain ⟨lift, hlift⟩ := hrestriction ⟨element, hmem⟩
  have htop : lift ∈ transfer.ker ⊔ (sylow : Subgroup preimage) := by
    rw [hcomplement]
    exact Subgroup.mem_top _
  obtain ⟨complementMember, hcomplementMember, kernelMember, hkernelMember, hproduct⟩ :=
    Subgroup.mem_sup_of_normal_left.mp htop
  have hkernelValue : restriction kernelMember = 1 := by
    apply MonoidHom.mem_ker.mp
    rwa [hsylow] at hkernelMember
  have hvalue : quotient complementMember.val = element := by
    have hrestrictionValue : restriction complementMember = ⟨element, hmem⟩ := by
      rw [← hlift, ← hproduct, map_mul, hkernelValue, mul_one]
    exact congrArg Subtype.val hrestrictionValue
  exact ⟨complementMember.val, hambientCoreLe ⟨complementMember, hcomplementMember, rfl⟩, hvalue⟩

noncomputable def coreQuotientMap {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient) :
    (G ⧸ componentClassificationOddCore G) →* (H ⧸ componentClassificationOddCore H) :=
  QuotientGroup.map _ _ quotient
    (Subgroup.map_le_iff_le_comap.mp (OddKernel.core_map_le quotient hsurjective))

theorem coreQuotientMap_apply_mk {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient) (element : G) :
    (coreQuotientMap quotient hsurjective) ((QuotientGroup.mk' (componentClassificationOddCore G)) element) =
      (QuotientGroup.mk' (componentClassificationOddCore H)) (quotient element) :=
  QuotientGroup.map_mk _ _ quotient _ element

theorem coreQuotientMap_surjective {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient) :
    Function.Surjective (coreQuotientMap quotient hsurjective) := by
  intro element
  obtain ⟨member, rfl⟩ := (QuotientGroup.mk'_surjective (componentClassificationOddCore H)) element
  obtain ⟨lift, rfl⟩ := hsurjective member
  exact ⟨(QuotientGroup.mk' (componentClassificationOddCore G)) lift,
    coreQuotientMap_apply_mk quotient hsurjective lift⟩

theorem coreQuotientMap_kernel_central {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) (htwoKernel : IsPGroup 2 quotient.ker) :
    (coreQuotientMap quotient hsurjective).ker ≤
      Subgroup.center (G ⧸ componentClassificationOddCore G) := by
  intro element hmem
  obtain ⟨member, rfl⟩ := (QuotientGroup.mk'_surjective (componentClassificationOddCore G)) element
  have hone := MonoidHom.mem_ker.mp hmem
  rw [coreQuotientMap_apply_mk] at hone
  have hcore : quotient member ∈ componentClassificationOddCore H :=
    (QuotientGroup.eq_one_iff _).mp hone
  rw [← core_image quotient hsurjective hcentralKernel htwoKernel] at hcore
  obtain ⟨coreMember, hcoreMember, hvalue⟩ := Subgroup.mem_map.mp hcore
  have hkernel : member * coreMember⁻¹ ∈ quotient.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hvalue, mul_inv_cancel]
  have hcentral := hcentralKernel hkernel
  have hcoreValue : (QuotientGroup.mk' (componentClassificationOddCore G)) coreMember = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hcoreMember
  have hrepresentative : (QuotientGroup.mk' (componentClassificationOddCore G)) member =
      (QuotientGroup.mk' (componentClassificationOddCore G)) (member * coreMember⁻¹) := by
    rw [map_mul, map_inv, hcoreValue, inv_one, mul_one]
  rw [hrepresentative]
  apply Subgroup.mem_center_iff.mpr
  intro other
  obtain ⟨lift, rfl⟩ := (QuotientGroup.mk'_surjective (componentClassificationOddCore G)) other
  simpa only [map_mul] using congrArg (QuotientGroup.mk' (componentClassificationOddCore G))
    ((Subgroup.mem_center_iff.mp hcentral) lift)

theorem quasisimple_of_surjective {G H : Type*} [Group G] [Group H]
    (hquasisimple : IsQuasisimple G) (quotient : G →* H)
    (hsurjective : Function.Surjective quotient) (hcentralKernel : quotient.ker ≤ Subgroup.center G) :
    IsQuasisimple H :=
  Components.quasisimple_of_equiv (QuotientGroup.liftEquiv quotient.ker hsurjective rfl).symm
    (Quasisimple.central_quotient hquasisimple quotient.ker hcentralKernel)

theorem residual_eq_top_of_two_kernel {G H : Type*} [Group G] [Finite G] [Group H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (htwoKernel : IsPGroup 2 quotient.ker) (hgenerated : TwoResidual.subgroup H = ⊤) :
    TwoResidual.subgroup G = ⊤ := by
  have hmap := TwoResidual.image_of_surjective quotient hsurjective
  rw [hgenerated] at hmap
  have hcomap := Subgroup.comap_map_eq quotient (TwoResidual.subgroup G)
  rw [hmap, Subgroup.comap_top] at hcomap
  have hkernelLe := TwoResidual.twoSubgroup_le quotient.ker htwoKernel
  exact top_unique (hcomap.trans_le (sup_le le_rfl hkernelLe))

end CFSG.ComponentClassification.CentralTwoKernel
