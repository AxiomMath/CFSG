module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Hyp
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IKFact
public import CFSG.Milestones.ASVolI.C135.WMain
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.MSPair
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Case2
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Case4
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IC134Excl
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IC134Block

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

namespace P614I

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem not_burnsideC135_Case4W (h : CampbellHyp X K R P) :
    ¬ CFSG.ASVolI.burnsideC135_Case4W X (pCoreOf 2 P) K := by
  rintro ⟨⟨n, F, _, _, α, hF, hα, hsum, hdisj, hU⟩, hNot, -⟩
  have hF2 := h.card_field_eq_two hF α hα
  exact false_of_notCentralizer h hNot (centralizer_omegaCenter_eq_of_center h
    (h.hasNatSection_of_case4 hF2 hα hsum hdisj hU) hdisj)

end P614I

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

theorem kFactCampbellBlock_of_asC134Weak
    (hC134 : CFSG.Quasithin.MS93.burnsideC134w_AS_C_1_34_corrOneWeak) : KFactCampbellBlock := by
  intro A _ _ X K R P hchar hKX hKnorm hKperf hXeq hquot hRX hR2 hRsyl hRP hPX hPidx hcent hpush
  have h : CampbellHyp X K R P :=
    ⟨hchar, hKX, hKnorm, hKperf, hXeq, hquot, hRX, hR2, hRsyl, hRP, hPX, hPidx, hcent, hpush⟩
  obtain ⟨F₀, _, _, α₀, hF₀, hα₀⟩ := h.exists_modO2Surj
  obtain ⟨i, hi⟩ := hC134 A X (pCoreOf 2 P) K h.isMSPair h.K_mem_cComp h.X_eq_mul
    ⟨F₀, inferInstance, inferInstance, α₀, hF₀, hα₀⟩
  rcases hi with ⟨hi4, hi⟩ | ⟨-, hi⟩
  · rcases i with _ | _ | _ | _ | _ | _ | i
    · exact hi.elim
    ·
      obtain ⟨-, n, F, _, _, hF, hnat⟩ := hi
      obtain ⟨α, hαs, hαk, hvia⟩ :=
        (CFSG.Quasithin.isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).1 hnat
      have hα : CFSG.Quasithin.IsModO2Surj K α := ⟨hαs, hαk⟩
      have hF2 := h.card_field_eq_two hF α hα
      exact P614I.blockConclusion_of_natural h (hasNatSection_of_via hF2 hα hvia)
    · exact (h.not_isC134Case2 hi).elim
    · exact (P614I.not_isC134Case3 h hi).elim
    · exact absurd rfl hi4
    · exact (P614I.not_isC134Case5 h hi).elim
    · exact hi.elim
  · exact (P614I.not_burnsideC135_Case4W h hi).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
