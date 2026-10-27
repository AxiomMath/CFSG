module

public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoLayerTransport

theorem equiv_invariant {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (equivalence : G ≃* H) :
    (TwoLayer.subgroup G).map equivalence.toMonoidHom = TwoLayer.subgroup H := by
  rw [← TwoLayer.good_sup_bad G, Subgroup.map_sup, TwoLayer.good_equiv_invariant equivalence,
    BadComponents.equiv_invariant equivalence, TwoLayer.good_sup_bad H]

theorem characteristic (G : Type*) [Group G] [Finite G] :
    (TwoLayer.subgroup G).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro automorphism
  exact equiv_invariant automorphism

theorem image_of_odd_kernel {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hodd : Odd (Nat.card quotient.ker)) :
    (TwoLayer.subgroup G).map quotient = TwoLayer.subgroup H := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro component hcomponent
    apply Subgroup.map_le_iff_le_comap.mp
    exact le_sSup (OddKernelTwoComponents.image quotient hsurjective hodd component hcomponent)
  · apply sSup_le
    intro component hcomponent
    obtain ⟨lift, hlift, hmap⟩ := OddKernelTwoComponents.exists_lift quotient hsurjective
      hodd component hcomponent
    rw [← hmap]
    exact Subgroup.map_mono (le_sSup hlift)

theorem ordinary_isTwoComponent_of_corefree {G : Type*} [Group G] [Finite G]
    (hcorefree : componentClassificationOddCore G = ⊥) (component : Subgroup G)
    (hcomponent : IsComponentOf component ⊤) : TwoComponents.IsTwoComponent component := by
  have hcomponentCore := OddCore.subnormal_corefree hcorefree component hcomponent.2.1
  apply (TwoComponentConvention.twoComponent_iff component).mpr
  refine ⟨hcomponent.2.1, QuasisimpleTwoGeneration.residual_eq_top_of_corefree
    hcomponent.2.2 hcomponentCore, ?_⟩
  let projection := QuotientGroup.mk' (componentClassificationOddCore component)
  have hkernel : projection.ker = ⊥ := by rw [QuotientGroup.ker_mk', hcomponentCore]
  let equivalence := MulEquiv.ofBijective projection
    ⟨(MonoidHom.ker_eq_bot_iff projection).mp hkernel, QuotientGroup.mk'_surjective _⟩
  exact Components.quasisimple_of_equiv equivalence.symm hcomponent.2.2

theorem eq_layer_of_corefree {G : Type*} [Group G] [Finite G]
    (hcorefree : componentClassificationOddCore G = ⊥) :
    TwoLayer.subgroup G = Layer.subgroup G := by
  apply le_antisymm
  · apply sSup_le
    intro component hcomponent
    exact Layer.component_le (TwoComponents.ordinary_of_corefree hcorefree hcomponent)
  · apply sSup_le
    intro component hcomponent
    exact le_sSup (ordinary_isTwoComponent_of_corefree hcorefree component hcomponent)

theorem core_quotient_image {G : Type*} [Group G] [Finite G] :
    (TwoLayer.subgroup G).map (QuotientGroup.mk' (componentClassificationOddCore G)) =
      Layer.subgroup (G ⧸ componentClassificationOddCore G) := by
  rw [image_of_odd_kernel (QuotientGroup.mk' (componentClassificationOddCore G))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact OddCore.odd_card G)]
  exact eq_layer_of_corefree (OddCore.quotient_corefree G)

theorem perfect_lift_from_core_quotient_layer {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (perfectSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup]
    (himage : perfectSubgroup.map (QuotientGroup.mk' (componentClassificationOddCore G)) ≤
      Layer.subgroup (G ⧸ componentClassificationOddCore G)) :
    perfectSubgroup ≤ TwoLayer.subgroup G := by
  let projection := QuotientGroup.mk' (componentClassificationOddCore G)
  let : Group.IsSolvable projection.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let : (TwoLayer.subgroup G).Characteristic := characteristic G
  apply SolvableKernelContainment.perfect_containment projection perfectSubgroup (TwoLayer.subgroup G)
  rwa [core_quotient_image]

end CFSG.ComponentClassification.TwoLayerTransport
