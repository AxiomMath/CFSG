module

public import CFSG.LocalAnalysis.ComponentClassification.CentralComponentQuotients
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayerTransport
public import CFSG.LocalAnalysis.ComponentClassification.LayerNormalStructure
public import CFSG.LocalAnalysis.ComponentClassification.LocalBNormalGeneration

public section

open CFSG.Open

namespace CFSG.ComponentClassification.PerfectCentralizingLayerLift

theorem normal_closure_centralizes {G : Type*} [Group G]
    (perfectSubgroup kernel : Subgroup G) [kernel.Normal]
    (hcentralizes : perfectSubgroup ≤ Subgroup.centralizer (kernel : Set G)) :
    Subgroup.normalClosure (perfectSubgroup : Set G) ≤
      Subgroup.centralizer (kernel : Set G) :=
  Subgroup.normalClosure_le_normal hcentralizes

theorem normal_closure_image_le {G H : Type*} [Group G] [Group H]
    (quotient : G →* H) (perfectSubgroup : Subgroup G)
    (himage : perfectSubgroup.map quotient ≤ Layer.subgroup H) :
    (Subgroup.normalClosure (perfectSubgroup : Set G)).map quotient ≤ Layer.subgroup H := by
  let : (Layer.subgroup H).Normal := Layer.normal H
  apply Subgroup.map_le_iff_le_comap.mpr
  exact Subgroup.normalClosure_le_normal (Subgroup.map_le_iff_le_comap.mp himage)

theorem enters_layer {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (perfectSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup]
    (hcentralizes : perfectSubgroup ≤ Subgroup.centralizer (quotient.ker : Set G))
    (himage : perfectSubgroup.map quotient ≤ Layer.subgroup H) :
    perfectSubgroup ≤ Layer.subgroup G := by
  let normalClosure := Subgroup.normalClosure (perfectSubgroup : Set G)
  let image := normalClosure.map quotient
  let : Group.IsPerfect normalClosure := LocalBNormalGeneration.perfect_normalClosure perfectSubgroup
  let : image.Normal := (inferInstance : normalClosure.Normal).map quotient hsurjective
  let : Group.IsPerfect image := Group.IsPerfect.map quotient
  have himageLayer := normal_closure_image_le quotient perfectSubgroup himage
  have hlayerTop : Layer.subgroup image = ⊤ :=
    LayerNormalStructure.layer_top_of_perfect_normal_contained image himageLayer
  let restriction : normalClosure →* image :=
    (quotient.domRestrict normalClosure).codRestrict image
      fun member => Subgroup.mem_map_of_mem quotient member.property
  have hrestriction : Function.Surjective restriction := by
    intro member
    obtain ⟨lift, hlift, hvalue⟩ := Subgroup.mem_map.mp member.property
    exact ⟨⟨lift, hlift⟩, Subtype.ext hvalue⟩
  have hclosureCentralizes := normal_closure_centralizes perfectSubgroup quotient.ker hcentralizes
  have hcentralKernel : restriction.ker ≤ Subgroup.center normalClosure := by
    intro member hmember
    have hkernel : member.val ∈ quotient.ker :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hmember)
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
      (hclosureCentralizes other.property) member.val hkernel).symm
  have hlayerImage := CentralComponentQuotients.layer_map restriction hrestriction hcentralKernel
  rw [hlayerTop] at hlayerImage
  have hclosureLayer : (⊤ : Subgroup normalClosure) ≤ Layer.subgroup normalClosure := by
    apply BadComponents.perfect_containment_of_central_kernel restriction hcentralKernel
    rw [hlayerImage]
    exact le_top
  have hlayerAmbient := LayerNormalStructure.normal_monotone normalClosure
  intro member hmember
  have hclosure : member ∈ normalClosure := Subgroup.subset_normalClosure hmember
  exact hlayerAmbient (Subgroup.mem_map_of_mem normalClosure.subtype
    (hclosureLayer (Subgroup.mem_top (⟨member, hclosure⟩ : normalClosure))))

theorem quotient_enters_layer {G : Type*} [Group G] [Finite G]
    (kernel perfectSubgroup : Subgroup G) [kernel.Normal] [Group.IsPerfect perfectSubgroup]
    (hcentralizes : ⁅perfectSubgroup, kernel⁆ = ⊥)
    (himage : perfectSubgroup.map (QuotientGroup.mk' kernel) ≤ Layer.subgroup (G ⧸ kernel)) :
    perfectSubgroup ≤ Layer.subgroup G := by
  apply enters_layer (QuotientGroup.mk' kernel) (QuotientGroup.mk'_surjective _) perfectSubgroup
  · rw [QuotientGroup.ker_mk']
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentralizes
  · exact himage

theorem twoLayer_enters_layer_of_core_centralization {G : Type*} [Group G] [Finite G]
    (perfectSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup]
    (hcentralizes : ⁅perfectSubgroup, componentClassificationOddCore G⁆ = ⊥)
    (htwoLayer : perfectSubgroup ≤ TwoLayer.subgroup G) :
    perfectSubgroup ≤ Layer.subgroup G := by
  apply quotient_enters_layer (componentClassificationOddCore G) perfectSubgroup hcentralizes
  have himage := Subgroup.map_mono
    (f := QuotientGroup.mk' (componentClassificationOddCore G)) htwoLayer
  rwa [TwoLayerTransport.core_quotient_image] at himage

end CFSG.ComponentClassification.PerfectCentralizingLayerLift
