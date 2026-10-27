module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.OutsideSigmaNormalizerRankTwoPlane
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

theorem FNI_rank_one_plane_centralizer_regular
    (h₁ : Statements.FNI_outside_sigma_plane_core_disjoint.{u}) :
    Statements.FNI_rank_one_plane_centralizer_regular.{u} := by
  intro G _ _ hG p M A E hA _hE _hAE q Q hq hqσ hrank hQ hQcard
  have := hG.isSimpleGroup
  have hQle : Q ≤ centralizer (A : Set G) := hQ.trans inf_le_right
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQcard
    exact hq.one_lt.ne hQcard
  have hQp : IsPGroup q Q := IsPGroup.of_card (by rw [pow_one, hQcard])
  have hNQ : ¬ normalizer (Q : Set G) ≤ M := by
    intro hle
    have h2 := elementaryAbelianPRank_eq_two_of_notMem_sigmaPrimes hG.not_isMulCommutative
      hG.odd_natCard hG.isSolvable_of_ne_top hA.isCoatom hq hqσ hQcard hle
    rw [hrank] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨L, hLcoatom, hNL⟩ := exists_isCoatom_ge_of_ne_top
    (normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hq hQne hQp).ne
  have hLM : L ≠ M := fun h => hNQ (h ▸ hNL)
  have hAL : A ≤ L :=
    ((le_centralizer_iff.2 hQle).trans (centralizer_le_normalizer _)).trans hNL
  have hdisj := h₁ G hG p M A L hA hLcoatom hLM hAL
  have hle : sigmaCore M ⊓ centralizer (Q : Set G) ≤ sigmaCore M ⊓ L :=
    inf_le_inf_left _ ((centralizer_le_normalizer _).trans hNL)
  rw [hdisj] at hle
  exact le_bot_iff.1 hle

end

end CFSG.FeitThompson.Proofs
