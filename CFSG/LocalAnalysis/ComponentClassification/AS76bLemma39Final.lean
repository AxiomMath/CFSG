module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma39

public section

namespace CFSG.ComponentClassification.AS76b

namespace Lemma39

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G : Type} [Group G] [Finite G]

theorem lemma39_one_of_lemma32
    (h32 : Lemma32)
    {A T : Subgroup G} {g t : G} (hA : Hyp31 A)
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) (ht : t ∈ T) (ht1 : t ≠ 1)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) :
    admResidual (oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
        ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆) ≤ rightConjugate A g ∧
      rightConjugate A g ≤ centralizer (T : Set G) :=
  lemma39_one RankTwoFoundation.asc75Theorem4 h32 asc08Lemma34 hA hT ht ht1 hOut

end Lemma39

end CFSG.ComponentClassification.AS76b
