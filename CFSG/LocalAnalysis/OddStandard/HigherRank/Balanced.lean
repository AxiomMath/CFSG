module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced
public import CFSG.GroupTheory.PCore.Defs
import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
import CFSG.ClassicalInvolution.OrderForm

public section

namespace CFSG.OddStandard.HigherRank

open CFSG.Blueprint

theorem catalog_of_uOutcome {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (h : ComponentClassification.OutcomeLocal.UOutcome G) : Catalog G := by
  have htop : ComponentClassification.GeneralizedFitting.subgroup G = ⊤ :=
    ComponentClassification.GSLit.generalizedFitting_eq_top_of_simple
  let e : ComponentClassification.GeneralizedFitting.subgroup G ≃* G :=
    ComponentClassification.GSLit.generalizedFittingEquivOfSimple
  rcases h with h | ⟨n, hodd, h7, ⟨eA⟩, h1⟩ | ⟨-, hlt⟩
  · rcases (ClassicalInvolution.oddLieType_congr e).1 h with ⟨t, n, p, f, hp, hp2, hadm, hm⟩
    exact lieModel_catalog G t n p f hm
  · exact Or.inr (Or.inl ⟨n, by omega, ⟨e.symm.trans eA⟩⟩)
  · exact absurd htop hlt.ne

theorem oddCore_eq_bot_of_not_catalog {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hU : (∃ z : G, orderOf z = 2 ∧
        CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) →
      ComponentClassification.OutcomeLocal.UOutcome G)
    (hcat : ¬ Catalog G) {z : G} (hz : orderOf z = 2) :
    CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
  by_contra hne
  exact hcat (catalog_of_uOutcome (hU ⟨z, hz, hne⟩))

end CFSG.OddStandard.HigherRank
