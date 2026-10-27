module

public import CFSG.LocalAnalysis.ComponentClassification.EvenSimpleTwoQuotientOddCore

public section

open CFSG.Open

namespace CFSG.ComponentClassification.NormalCenterQuotientImage

@[expose] noncomputable def equivalence {G : Type*} [Group G]
    (ambient kernel : Subgroup G) [kernel.Normal]
    (hkernel : kernel.subgroupOf ambient = Subgroup.center ambient) :
    ambient ⧸ Subgroup.center ambient ≃* ambient.map (QuotientGroup.mk' kernel) := by
  let quotient := QuotientGroup.mk' kernel
  let image := ambient.map quotient
  let homomorphism := (quotient.comp ambient.subtype).codRestrict image
    (fun member => Subgroup.mem_map.mpr ⟨member.val, member.property, rfl⟩)
  have hsurjective : Function.Surjective homomorphism := by
    intro member
    obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp member.property
    exact ⟨⟨lift, hlift⟩, Subtype.ext heq⟩
  have hhomKernel : homomorphism.ker = Subgroup.center ambient := by
    rw [← hkernel]
    ext member
    change (⟨quotient member.val, _⟩ : image) = 1 ↔ member.val ∈ kernel
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  exact QuotientGroup.liftEquiv _ hsurjective hhomKernel.symm

theorem quotient_two {G : Type*} [Group G]
    (ambient kernel : Subgroup G) [ambient.Normal] [kernel.Normal]
    (htwo : IsPGroup 2 (G ⧸ ambient)) :
    IsPGroup 2 ((G ⧸ kernel) ⧸ ambient.map (QuotientGroup.mk' kernel)) := by
  let quotient := QuotientGroup.mk' kernel
  let image := ambient.map quotient
  let homomorphism := (QuotientGroup.mk' image).comp quotient
  have hkernel : ambient ≤ homomorphism.ker := by
    intro member hmember
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)
  let induced := QuotientGroup.lift ambient homomorphism hkernel
  have hsurjective : Function.Surjective induced := by
    intro member
    obtain ⟨lift, hlift⟩ := ((QuotientGroup.mk'_surjective image).comp (QuotientGroup.mk'_surjective kernel)) member
    refine ⟨(QuotientGroup.mk' ambient) lift, ?_⟩
    exact (congrArg (fun hom : G →* (G ⧸ kernel) ⧸ image => hom lift)
      (QuotientGroup.lift_comp_mk' ambient homomorphism hkernel)).trans hlift
  exact htwo.of_surjective induced hsurjective

theorem odd_core_trivial {G : Type*} [Group G] [Finite G]
    (ambient kernel : Subgroup G) [ambient.Normal] [kernel.Normal]
    (hquasisimple : IsQuasisimple ambient) (heven : Even (Nat.card ambient))
    (hkernel : kernel.subgroupOf ambient = Subgroup.center ambient)
    (htwo : IsPGroup 2 (G ⧸ ambient)) : componentClassificationOddCore (G ⧸ kernel) = ⊥ := by
  let image := ambient.map (QuotientGroup.mk' kernel)
  let equivalence := equivalence ambient kernel hkernel
  let : IsSimpleGroup (ambient ⧸ Subgroup.center ambient) := hquasisimple.2
  let : IsSimpleGroup image := equivalence.symm.isSimpleGroup
  let : Group.IsPerfect ambient := ⟨hquasisimple.1⟩
  have hevenImage : Even (Nat.card image) := by
    rw [← Nat.card_congr equivalence.toEquiv]
    exact PerfectCentralQuotient.even_central_quotient heven
  exact EvenSimpleTwoQuotientOddCore.trivial image hevenImage (quotient_two ambient kernel htwo)

end CFSG.ComponentClassification.NormalCenterQuotientImage
