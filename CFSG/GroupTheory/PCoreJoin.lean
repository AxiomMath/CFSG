module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem pCoreOf_sup_le_pCoreOf_sup {p : ℕ} [Fact p.Prime] {Y U : Subgroup G}
    (hU : IsPGroup p U) (hYU : Y ≤ normalizer (U : Set G)) :
    CFSG.Open.pCoreOf p Y ⊔ U ≤ CFSG.Open.pCoreOf p (Y ⊔ U) := by
  have hO := CFSG.LieType.BorelTits.pCoreOf_le p Y
  have hW : IsPGroup p ↥(CFSG.Open.pCoreOf p Y ⊔ U) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup p Y).to_sup_of_normal_right' hU (hO.trans hYU)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
    (sup_le (hO.trans le_sup_left) le_sup_right) (sup_le ?_ (le_sup_right.trans le_normalizer)) hW
  exact (le_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p Y) hYU).trans
    (inf_normalizer_le_normalizer_sup _ _)

end CFSG.GroupTheory
