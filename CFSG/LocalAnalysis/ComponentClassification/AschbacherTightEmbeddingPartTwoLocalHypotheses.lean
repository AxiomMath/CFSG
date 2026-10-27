module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoData

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G] [Finite G]

theorem point_class_commuting_product_mem_Q (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (t : G) (ht : t ∈ involutionPointClass z) (hne : z ≠ t) (hcomm : Commute z t) :
    z * t ∈ Q ∧ orderOf (z * t) = 2 := by
  obtain ⟨hprod, horder, _⟩ :=
    class_product_unique_containment Q hodd z t hzQ hz ht hcomm.symm hne.symm
  simpa only [hcomm.eq] using (show t * z ∈ Q ∧ orderOf (t * z) = 2 from ⟨hprod, horder⟩)

theorem point_class_commuting_product_unique_containment (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (t : G) (ht : t ∈ involutionPointClass z) (hne : z ≠ t) (hcomm : Commute z t) :
    ∀ g : G, g⁻¹ * (z * t) * g ∈ Subgroup.normalizer (Q : Set G) ↔
      g ∈ Subgroup.normalizer (Q : Set G) := by
  obtain ⟨hprod, horder⟩ :=
    point_class_commuting_product_mem_Q Q hodd z hzQ hz t ht hne hcomm
  exact involution_conjugate_mem_normalizer_iff Q hodd (z * t) hprod horder

theorem point_class_commuting_product_centralizer_le (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (t : G) (ht : t ∈ involutionPointClass z) (hne : z ≠ t) (hcomm : Commute z t) :
    Subgroup.centralizer ({z * t} : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  obtain ⟨hprod, horder⟩ :=
    point_class_commuting_product_mem_Q Q hodd z hzQ hz t ht hne hcomm
  exact involution_centralizer_le_normalizer Q hodd (z * t) hprod horder

theorem theorem_three_three_original_hypotheses (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal) :
    ∃ (P : Sylow 2 G) (z : G),
      Subgroup.normalizer (Q : Set G) ≠ ⊤ ∧ z ∈ Q ∧ orderOf z = 2 ∧
      z ∈ (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ∧
      (∀ g : G, z ∈ rightConjugate (Subgroup.normalizer (Q : Set G)) g ↔
        g ∈ Subgroup.normalizer (Q : Set G)) ∧
      (∀ t ∈ involutionPointClass z, z ≠ t → Commute z t →
        ∀ g : G, g⁻¹ * (z * t) * g ∈ Subgroup.normalizer (Q : Set G) ↔
          g ∈ Subgroup.normalizer (Q : Set G)) ∧
      (∀ t ∈ involutionPointClass z, z ≠ t → Commute z t →
        Subgroup.centralizer ({z * t} : Set G) ≤ Subgroup.normalizer (Q : Set G)) := by
  obtain ⟨P, z, hzQ, hz, _, hzcenter, _⟩ :=
    exists_central_sylow_involution_in_Q Q htight hodd
  refine ⟨P, z, ?_, hzQ, hz, hzcenter,
    involution_unique_containing_normalizer Q hodd z hzQ hz, ?_, ?_⟩
  · exact fun htop => hnormal (Subgroup.normalizer_eq_top_iff.mp htop)
  · intro t ht hne hcomm
    exact point_class_commuting_product_unique_containment Q hodd z hzQ hz t ht hne hcomm
  · intro t ht hne hcomm
    exact point_class_commuting_product_centralizer_le Q hodd z hzQ hz t ht hne hcomm

end CFSG.ComponentClassification.AschbacherTightEmbedding
