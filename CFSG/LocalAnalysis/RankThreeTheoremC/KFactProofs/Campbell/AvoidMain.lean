module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.MSPair
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Natural
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Case2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Case4
public import CFSG.Milestones.ASVolI.C135.WMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem CampbellHyp.conclusion_of_caseWeak (h : CampbellHyp X K R P) {i : ℕ}
    (hi : CFSG.Quasithin.MS93.burnsideC134w_CaseWeak i X (pCoreOf 2 P) K) :
    CampbellConclusion X K := by
  obtain ⟨hbotK, hbotX⟩ := bot_conditions X K
  obtain ⟨hcK, hcX⟩ := h.c134CQ_conditions
  rcases hi with ⟨-, hi⟩ | ⟨-, hi⟩
  · rcases i with _ | _ | _ | _ | _ | _ | i
    · exact hi.elim
    ·
      obtain ⟨-, n, F, _, _, hF, hnat⟩ := hi
      obtain ⟨α, hαs, hαk, hvia⟩ :=
        (CFSG.Quasithin.isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).1 hnat
      have hα : CFSG.Quasithin.IsModO2Surj K α := ⟨hαs, hαk⟩
      have hF2 := h.card_field_eq_two hF α hα
      exact h.conclusion_of_hasNatSection (D := CFSG.Quasithin.c134Q X K) (C₀ := ⊥)
        inf_le_left hbotK hbotX (hasNatSection_of_via hF2 hα hvia)
    ·
      exact (h.not_isC134Case2 hi).elim
    ·
      obtain ⟨⟨n, F, _, _, α, hF, hα, hvia, -⟩, -⟩ := hi
      have hF2 := h.card_field_eq_two hF α hα
      exact h.conclusion_of_hasNatSection
        (D := CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K)) (C₀ := ⊥) le_rfl hbotK hbotX
        (hasNatSection_of_via hF2 hα hvia)
    ·
      obtain ⟨⟨n, F, _, _, α, hF, hα, -, hsum, hdisj, hU, -⟩, -⟩ := hi
      have hF2 := h.card_field_eq_two hF α hα
      exact h.conclusion_of_hasNatSection
        (D := CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K))
        (C₀ := CFSG.Quasithin.c134CQ X K) le_rfl hcK hcX
        (h.hasNatSection_of_case4 hF2 hα hsum hdisj hU)
    ·
      obtain ⟨⟨α, hα, -, hvia⟩, -⟩ := hi
      exact h.conclusion_of_hasNatSection (D := CFSG.Quasithin.c134Q X K)
        (C₀ := CFSG.Quasithin.c134CQ X K) inf_le_left hcK hcX
        (hasNatSection_of_via (F := ZMod 2) (by simp) hα hvia)
    · exact hi.elim
  ·
    obtain ⟨⟨n, F, _, _, α, hF, hα, hsum, hdisj, hU⟩, -, -⟩ := hi
    have hF2 := h.card_field_eq_two hF α hα
    exact h.conclusion_of_hasNatSection
      (D := CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q X K))
      (C₀ := CFSG.Quasithin.c134CQ X K) le_rfl hcK hcX
      (h.hasNatSection_of_case4 hF2 hα hsum hdisj hU)

theorem kFactCampbell_of_asC134Weak
    (hC134 : CFSG.Quasithin.MS93.burnsideC134w_AS_C_1_34_corrOneWeak) : KFactCampbell := by
  intro A _ _ X K R P hchar hKX hKnorm hKperf hXeq hquot hRX hR2 hRsyl hRP hPX hPidx hcent hpush
  have h : CampbellHyp X K R P :=
    ⟨hchar, hKX, hKnorm, hKperf, hXeq, hquot, hRX, hR2, hRsyl, hRP, hPX, hPidx, hcent, hpush⟩
  obtain ⟨F₀, _, _, α₀, hF₀, hα₀⟩ := h.exists_modO2Surj
  obtain ⟨i, hi⟩ := hC134 A X (pCoreOf 2 P) K h.isMSPair h.K_mem_cComp h.X_eq_mul
    ⟨F₀, inferInstance, inferInstance, α₀, hF₀, hα₀⟩
  exact h.conclusion_of_caseWeak hi
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
