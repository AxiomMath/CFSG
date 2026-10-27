module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsSDModels
public import CFSG.Milestones.LR_semidihedral_simple_recognition

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsSD

open CFSG.Open

theorem simpleFixedInvolutionPair_holds : SimpleFixedInvolutionPair := by
  intro X _ _ _ hnonab hsd α hα
  rcases CFSG.Milestones.lr_semidihedral_simple_recognition_1 X hnonab hsd with
    ⟨p, f, -, hp2, -, -, hm⟩ | ⟨p, f, -, hp2, -, -, hm⟩ | hm
  · exact psl_three_fixed_involution_pair hp2 hm α hα
  · exact psu_three_fixed_involution_pair hp2 hm α hα
  · exact m11_fixed_involution_pair hnonab hsd hm α hα

theorem semidihedral_four_group_holds : ∀ (G : Type) [Group G] [Finite G] (L U : Subgroup G),
    Open.IsQuasisimple L → HasSemidihedralSylowTwo L → U ≤ Subgroup.normalizer (L : Set G) →
    IsFourGroup U → ∃ u ∈ U, u ≠ 1 ∧ 2 ≤ Open.pRank 2 (L ⊓ Subgroup.centralizer ({u} : Set G)) :=
  semidihedral_four_group_of_simple simpleFixedInvolutionPair_holds

theorem semidihedral_no_cyclic_four_holds : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G)
    (a : G), Open.IsQuasisimple L → HasSemidihedralSylowTwo L →
    a ∈ Subgroup.normalizer (L : Set G) → a ^ 2 = 1 →
    ∀ P : Sylow 2 ↥(L ⊓ Subgroup.centralizer ({a} : Set G)),
      ¬ (IsCyclic (P : Subgroup ↥(L ⊓ Subgroup.centralizer ({a} : Set G))) ∧ Nat.card P = 4) :=
  semidihedral_no_cyclic_four_of_simple simpleFixedInvolutionPair_holds

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsSD
