module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierCoreBranches
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem isCyclic_sylow_of_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H K : Subgroup G} (hHK : H ≤ K) (hK : ∀ P : Sylow p ↥K, IsCyclic (P : Subgroup ↥K))
    (P : Sylow p ↥H) : IsCyclic (P : Subgroup ↥H) := by
  set Q : Subgroup ↥K := (P : Subgroup ↥H).map (Subgroup.inclusion hHK)
  obtain ⟨R, hQR⟩ := (P.isPGroup'.map (Subgroup.inclusion hHK)).exists_le_sylow
  have := hK R
  have hQ : IsCyclic Q := Subgroup.isCyclic_of_le hQR
  exact ((P : Subgroup ↥H).equivMapOfInjective (Subgroup.inclusion hHK)
    (Subgroup.inclusion_injective hHK)).isCyclic.mpr hQ

theorem harrisInput_of_theoremOne (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (h1 : TheoremOne) : GSLit.HarrisInput := by
  rintro X _ _ _ hnonab hK hz hU ⟨x, L, hx, hLx, hL, -, ⟨p, f, hp, hp2, hf, h5, hm⟩, hcyc⟩
  have hc : Config x L p f :=
    ⟨hx, hLx, hL, hp, hp2, hf, h5, hm, isCyclic_sylow_of_le inf_le_right hcyc⟩
  exact hU (UFrontier.uOutcome_of_catalog hCU hnonab (h1 X hnonab hK x L p f hc) hz)

end CFSG.ComponentClassification.HarrisLit
