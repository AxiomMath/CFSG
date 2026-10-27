module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusionZStar

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion

open CFSG.ShultStronglyClosedTI CFSG.Open
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

universe v

variable {G : Type v} [Group G]

@[expose] def ambientInvolutionClasses (G : Type v) [Group G] : Set (ConjClasses G) :=
  ConjClasses.mk '' {x : G | orderOf x = 2}

theorem conjClasses_eq_iff_pointClass {a b : G} :
    ConjClasses.mk a = ConjClasses.mk b ↔ a ∈ involutionPointClass b := by
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_comm, isConj_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, by simpa only [rightConjugateElem, inv_inv] using hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, by simpa only [rightConjugateElem, inv_inv] using hg⟩

theorem ThreeLocalOrbitData.translate_subset_class_intersection [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {u z : G} {T : Sylow 2 (Subgroup.centralizer ({u} : Set G))}
    {U : Subgroup G} (h : ThreeLocalOrbitData u T U z) :
    involutionTranslate u U ⊆ involutionPointClass u ∩
      (centralizerSylowImage u T : Set G) := by
  have hclasses := point_class_eq_of_mem (h.product_fused hnonab)
  rintro x ⟨w, hwU, rfl⟩
  refine ⟨?_, (centralizerSylowImage u T).mul_mem
    (involution_mem_centralizerSylowImage h.involution_order T) (h.subgroup_le hwU)⟩
  by_cases hw : w = 1
  · simpa only [hw, mul_one] using distinguished_mem_pointClass u
  · exact hclasses ▸ h.product_orbit (show u * w ∈
      (fun w : G => u * w) '' puncturedSubgroup U from ⟨w, ⟨hwU, hw⟩, rfl⟩)

theorem ThreeLocalOrbitData.class_intersection_eq_translate [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {u z : G} {T : Sylow 2 (Subgroup.centralizer ({u} : Set G))}
    {U : Subgroup G} (h : ThreeLocalOrbitData u T U z) :
    involutionPointClass u ∩ (centralizerSylowImage u T : Set G) =
      involutionTranslate u U := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxinv : x ∈ subgroupInvolutions (centralizerSylowImage u T) :=
      ⟨hx.2, order_two_of_mem_pointClass h.involution_order hx.1⟩
    rw [h.full_partition] at hxinv
    rcases hxinv with (hxu | hxU) | hxproduct
    · have hxu' : x = u := Set.mem_singleton_iff.mp hxu
      exact ⟨1, U.one_mem, by simpa only [mul_one] using hxu'.symm⟩
    · exact (Set.disjoint_left.mp (full_point_classes_disjoint u z h.distinct_classes)
        hx.1 (h.distinguished_orbit hxU)).elim
    · obtain ⟨w, hw, rfl⟩ := hxproduct
      exact ⟨w, hw.1, rfl⟩
  · exact h.translate_subset_class_intersection hnonab

theorem ThreeLocalOrbitData.every_involution_in_two_classes [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {u z : G} {T : Sylow 2 (Subgroup.centralizer ({u} : Set G))}
    {U : Subgroup G} (h : ThreeLocalOrbitData u T U z)
    (hinto : ∀ x : G, orderOf x = 2 → ∃ g : G,
      rightConjugateElem x g ∈ centralizerSylowImage u T) :
    ∀ x : G, orderOf x = 2 →
      x ∈ involutionPointClass u ∨ x ∈ involutionPointClass z := by
  have hclasses := point_class_eq_of_mem (h.product_fused hnonab)
  intro x hx
  obtain ⟨g, hg⟩ := hinto x hx
  have hxinv : rightConjugateElem x g ∈
      subgroupInvolutions (centralizerSylowImage u T) :=
    ⟨hg, order_two_of_mem_pointClass hx (show rightConjugateElem x g ∈
      involutionPointClass x from ⟨g, rfl⟩)⟩
  rw [h.full_partition] at hxinv
  have hundo : rightConjugateElem (rightConjugateElem x g) g⁻¹ = x := by
    simp only [rightConjugateElem, inv_inv, mul_assoc,
      mul_inv_cancel_left, mul_inv_cancel, mul_one]
  rcases hxinv with (hxu | hxU) | hxproduct
  · left
    have hc : rightConjugateElem x g ∈ involutionPointClass u :=
      (Set.mem_singleton_iff.mp hxu).symm ▸ distinguished_mem_pointClass u
    exact hundo ▸ pointClass_right_conjugate_mem hc g⁻¹
  · right
    exact hundo ▸ pointClass_right_conjugate_mem (h.distinguished_orbit hxU) g⁻¹
  · left
    exact hundo ▸ pointClass_right_conjugate_mem (hclasses ▸ h.product_orbit hxproduct) g⁻¹

theorem ThreeLocalOrbitData.all_involutions_eq_two_classes [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {u z : G} {T : Sylow 2 (Subgroup.centralizer ({u} : Set G))}
    {U : Subgroup G} (h : ThreeLocalOrbitData u T U z)
    (hinto : ∀ x : G, orderOf x = 2 → ∃ g : G,
      rightConjugateElem x g ∈ centralizerSylowImage u T) :
    {x : G | orderOf x = 2} = involutionPointClass u ∪ involutionPointClass z := by
  ext x
  constructor
  · exact h.every_involution_in_two_classes hnonab hinto x
  · rintro (hx | hx)
    · exact order_two_of_mem_pointClass h.involution_order hx
    · exact order_two_of_mem_pointClass h.distinguished_order hx

theorem ThreeLocalOrbitData.ambient_involution_classes_eq_pair [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {u z : G} {T : Sylow 2 (Subgroup.centralizer ({u} : Set G))}
    {U : Subgroup G} (h : ThreeLocalOrbitData u T U z)
    (hinto : ∀ x : G, orderOf x = 2 → ∃ g : G,
      rightConjugateElem x g ∈ centralizerSylowImage u T) :
    ambientInvolutionClasses G = {ConjClasses.mk u, ConjClasses.mk z} := by
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases h.every_involution_in_two_classes hnonab hinto x hx with hxU | hxZ
    · exact Set.mem_insert_iff.mpr (Or.inl (conjClasses_eq_iff_pointClass.mpr hxU))
    · exact Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_singleton_iff.mpr (conjClasses_eq_iff_pointClass.mpr hxZ)))
  · intro hC
    rcases Set.mem_insert_iff.mp hC with rfl | hC
    · exact ⟨u, h.involution_order, rfl⟩
    · have hCz := Set.mem_singleton_iff.mp hC
      exact ⟨z, h.distinguished_order, hCz.symm⟩

theorem ThreeLocalOrbitData.ambient_involution_classes_ncard [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {u z : G} {T : Sylow 2 (Subgroup.centralizer ({u} : Set G))}
    {U : Subgroup G} (h : ThreeLocalOrbitData u T U z)
    (hinto : ∀ x : G, orderOf x = 2 → ∃ g : G,
      rightConjugateElem x g ∈ centralizerSylowImage u T) :
    (ambientInvolutionClasses G).ncard = 2 := by
  rw [h.ambient_involution_classes_eq_pair hnonab hinto]
  exact Set.ncard_pair (fun heq => h.distinct_classes (conjClasses_eq_iff_pointClass.mp heq))

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion
