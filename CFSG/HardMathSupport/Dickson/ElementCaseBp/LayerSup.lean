module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.HardMathSupport.Dickson.ElementCaseBp

theorem layer_le_sup_centralizer {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : CFSG.IsComponent K) : CFSG.layer G ≤ K ⊔ Subgroup.centralizer (K : Set G) := by
  rw [CFSG.layer.eq_sSup]
  refine sSup_le fun K' hK' => ?_
  by_cases h : K' = K
  · rw [h]
    exact le_sup_left
  · refine le_sup_of_le_right ?_
    rcases CFSG.LocalCores.distinct_components_commute (hK' : CFSG.IsComponent K') hK with h' | h'
    · exact absurd h' h
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h'

end CFSG.HardMathSupport.Dickson.ElementCaseBp
