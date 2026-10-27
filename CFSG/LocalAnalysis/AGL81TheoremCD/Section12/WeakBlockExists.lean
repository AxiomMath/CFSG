module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NoXBlockGen
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

theorem weakBlockSet_nonempty
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h84 : CFSG.AGLEmbedding.Asc81bEightFour)
    (h : TwelveCtx G M p Q H) : (weakBlockSet M H).Nonempty := by
  haveI : IsSimpleGroup G := h.cstar.simple
  have hmaxH : GLBIsMaxTwoLocal H := by
    refine ⟨h.H_twoLocal, fun K hK hHK => h.H_mem_H2Star.2 K ?_ hHK⟩
    refine ⟨twoLocal_ne_top h.cstar.nonab K hK, h.Q_le_H.trans hHK, ?_, ?_⟩
    · exact fun hKM => h.not_H_le_M (hHK.trans hKM)
    · exact h.cstar.charTwo K hK
  have hSleM : pCoreOf 2 H ≤ M := by
    rw [h.pCore_two_inter]
    exact (pCoreOf_le 2 _).trans inf_le_right
  have hpair : TwoLocalPair M H :=
    { maxTwoLocal_M := h.maxLocal
      maxTwoLocal_H := hmaxH
      not_le := h.not_H_le_M
      twoCore_le := hSleM }
  have hNH : Subgroup.normalizer (pCoreOf 2 H : Set G) = H :=
    (maxTwoLocal_eq_normalizer_pCoreOf H hmaxH).symm
  have hA : Asc81bHyp M (pCoreOf 2 H) :=
    { twoRadical :=
        ⟨hSleM, twoLocal_pCoreOf_ne_bot H h.H_twoLocal, by
          rw [hNH, inf_comm]
          exact h.pCore_two_inter⟩
      charTwo := h.cstar.charTwo M h.maxLocal.1
      cgs := by rw [maxTwoLocal_cgsIn_eq_inf hmaxH M, hNH] }
  have hMtop : M ≠ ⊤ := twoLocal_ne_top h.cstar.nonab M h.maxLocal.1
  have hK : CFSG.Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper hMtop
  have hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G :=
    noXBlockFor_of_standingGen h1 h2 h25 h.cstar.toStandingGen
  have hoddCore := hA.oddCore_le_centralizer hK h.maxLocal h84 hD2
  rcases hpair.exists_weakSBlock_or_oddCore h.pCore_two_inter.symm with ⟨L, hL⟩ | hodd
  · exact ⟨L, hL⟩
  · exact (hodd hoddCore).elim

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
