module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Simple
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21L2

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

theorem lemma21 (h4 : Asc75Theorem4) {G : Type} [Group G] [Finite G] {K R : Subgroup G}
    (hK : TightlyEmbedded K) (hR : IsSylowOf 2 R K) (hRe : IsElemAbelian 2 R)
    (hF : IsSimpleGroup (CFSG.generalizedFitting G)) (hKn : ¬ K.Normal) :
    TightlyEmbedded (oddCoreIn K ⊔ R) ∧
      ∀ r ∈ R, r ≠ 1 → Group.IsSolvable (K ⊓ centralizer ({r} : Set G) : Subgroup G) := by
  by_cases hA : twoPrimeLayerIn K = oddCoreIn K
  · obtain ⟨hTE, hsolv⟩ := tightlyEmbedded_and_isSolvable_of_twoElements hK hR
      (twoElements_le_of_layer_eq_bot hR hRe ((twoPrimeLayerIn_eq_oddCoreIn_iff K).mp hA))
    exact ⟨hTE, fun r _ _ => Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : K ⊓ centralizer ({r} : Set G) ≤ K))⟩
  · rcases h4 G K hK hA with hB | ⟨h1, -⟩ | ⟨g, hg, T, hT, hTN, n, hn, φ, hφ, hker⟩
    · exact (false_of_normalIn_twoPrimeLayerIn_top hK hKn hF hA hB).elim
    · exact (false_of_pRank_twoPrimeLayerIn_eq_one hR hRe hA h1).elim
    · exact lemma21_caseD hK hR hRe hg hT hTN rfl hn φ hφ hker

end CFSG.ComponentClassification.AS76b
