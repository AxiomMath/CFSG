module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusionClasses

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion

open CFSG.ShultStronglyClosedTI CFSG.Open
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

universe v

variable {G : Type v} [Group G] [Finite G] [IsSimpleGroup G]

theorem three_local_involution_orbits_fusion
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (u : G) (hu : orderOf u = 2)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (U : Subgroup G) (hUelem : IsElementaryAbelian 2 U) (hUnontrivial : U ≠ ⊥)
    (hUT : U ≤ centralizerSylowImage u T)
    (z : G) (hzU : z ∈ U) (hz1 : z ≠ 1) (huU : u ∉ U)
    (hpartition : {x : G | x ∈ centralizerSylowImage u T ∧ orderOf x = 2} =
      ({u} : Set G) ∪ {w : G | w ∈ U ∧ w ≠ 1} ∪
        (fun w : G => u * w) '' {w : G | w ∈ U ∧ w ≠ 1})
    (hUclass : {w : G | w ∈ U ∧ w ≠ 1} ⊆ involutionPointClass z)
    (hproductclass : (fun w : G => u * w) '' {w : G | w ∈ U ∧ w ≠ 1} ⊆
      involutionPointClass (u * z))
    (hclasses : u ∉ involutionPointClass z) :
    u * z ∈ involutionPointClass u ∧
      involutionPointClass u ∩ (centralizerSylowImage u T : Set G) =
        (fun w : G => u * w) '' (U : Set G) := by
  have h : ThreeLocalOrbitData u T U z :=
    ⟨hu, hUelem, hUnontrivial, hUT, hzU, hz1, huU, hpartition,
      hUclass, hproductclass, hclasses⟩
  exact ⟨h.product_fused hnonab, h.class_intersection_eq_translate hnonab⟩

theorem three_local_involution_orbits_Zstar_fusion
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (u : G) (hu : orderOf u = 2)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (U : Subgroup G) (hUelem : IsElementaryAbelian 2 U) (hUnontrivial : U ≠ ⊥)
    (hUT : U ≤ centralizerSylowImage u T)
    (z : G) (hzU : z ∈ U) (hz1 : z ≠ 1) (huU : u ∉ U)
    (hpartition : {x : G | x ∈ centralizerSylowImage u T ∧ orderOf x = 2} =
      ({u} : Set G) ∪ {w : G | w ∈ U ∧ w ≠ 1} ∪
        (fun w : G => u * w) '' {w : G | w ∈ U ∧ w ≠ 1})
    (hUclass : {w : G | w ∈ U ∧ w ≠ 1} ⊆ involutionPointClass z)
    (hproductclass : (fun w : G => u * w) '' {w : G | w ∈ U ∧ w ≠ 1} ⊆
      involutionPointClass (u * z))
    (hclasses : u ∉ involutionPointClass z) :
    u * z ∈ involutionPointClass u ∧
      involutionPointClass u ∩ (centralizerSylowImage u T : Set G) =
        (fun w : G => u * w) '' (U : Set G) ∧
      (involutionPointClass u).Nonempty ∧ (involutionPointClass z).Nonempty ∧
      Disjoint (involutionPointClass u) (involutionPointClass z) ∧
      involutionPointClass u ≠ involutionPointClass z ∧
      ((∀ x : G, orderOf x = 2 → ∃ g : G,
        g⁻¹ * x * g ∈ centralizerSylowImage u T) →
        {x : G | orderOf x = 2} = involutionPointClass u ∪ involutionPointClass z ∧
        ambientInvolutionClasses G = {ConjClasses.mk u, ConjClasses.mk z} ∧
        (ambientInvolutionClasses G).ncard = 2 ∧
        Nat.card (ambientInvolutionClasses G) = 2) := by
  have h : ThreeLocalOrbitData u T U z :=
    ⟨hu, hUelem, hUnontrivial, hUT, hzU, hz1, huU, hpartition,
      hUclass, hproductclass, hclasses⟩
  refine ⟨h.product_fused hnonab, h.class_intersection_eq_translate hnonab,
    ⟨u, distinguished_mem_pointClass u⟩, ⟨z, distinguished_mem_pointClass z⟩,
    full_point_classes_disjoint u z hclasses, full_point_classes_ne u z hclasses, ?_⟩
  intro hinto
  have hncard := h.ambient_involution_classes_ncard hnonab hinto
  refine ⟨h.all_involutions_eq_two_classes hnonab hinto,
    h.ambient_involution_classes_eq_pair hnonab hinto, hncard, ?_⟩
  exact (Nat.card_coe_set_eq (ambientInvolutionClasses G)).trans hncard

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion
