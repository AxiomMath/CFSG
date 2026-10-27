module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrNormalClosure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSABasic

public section

namespace CFSG.ComponentClassification.UGSChain

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exists_sylow_two_le {H E : Subgroup G} (hEH : E ≤ H) (hE : IsPGroup 2 E) :
    ∃ S : Subgroup G, S ≤ H ∧ (∃ P : Sylow 2 ↥H, (P : Subgroup H) = S.subgroupOf H) ∧ E ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE' : IsPGroup 2 (E.subgroupOf H) := hE.comap_subtype
  obtain ⟨P, hP⟩ := hE'.exists_le_sylow
  refine ⟨(P : Subgroup H).map H.subtype, map_subtype_le _,
    ⟨P, (comap_map_eq_self_of_injective H.subtype_injective _).symm⟩, fun e he => ?_⟩
  exact ⟨⟨e, hEH he⟩, hP (show (⟨e, hEH he⟩ : H) ∈ E.subgroupOf H from he), rfl⟩

end CFSG.ComponentClassification.UGSChain
