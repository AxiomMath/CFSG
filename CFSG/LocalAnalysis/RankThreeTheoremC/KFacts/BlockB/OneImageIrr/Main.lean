module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Ctx
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLie
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieFinal
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8ParabolicBasic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutD4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

namespace OneImageIrr

theorem three_coprime_center_of_isOmegaEightPlus (hG : GriessAllModelsStatement) {X₀ : Type}
    [Group X₀] [Finite X₀] (hperf : Group.IsPerfect X₀)
    (h : IsOmegaEightPlus (X₀ ⧸ Subgroup.center X₀)) :
    Nat.Coprime 3 (Nat.card (Subgroup.center X₀)) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3
  have hdvd := card_center_dvd_card_griessHopfMultiplier hperf (MulEquiv.refl _)
  obtain ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩ := h
  have hcl : IsClassicalOrG2IndexTwo d.1 := by
    rw [hd]
    exact hq
  obtain ⟨r, q', hr, -, -⟩ :=
    three_dvd_multiplier_classicalIndexTwo hG d hcl e (h3.trans hdvd)
  rw [hd] at hr
  cases hr

theorem not_isOmegaEightPlus_of_pRank_le_three (hG : GriessAllModelsStatement) {G : Type}
    [Group G] [Finite G] {M L : Subgroup G} (hLM : L ≤ M) (hLL : ⁅L, L⁆ = L)
    (hM3 : Open.pRank 3 M ≤ 3) :
    ¬ IsOmegaEightPlus (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
  intro hO
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect ↥(barM M L) :=
    Subgroup.isPerfect_iff.mpr
      (CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.barM_perfect hLM hLL)
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (three_coprime_center_of_isOmegaEightPlus hG hperf hO)
  have h4 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.d4ThreeRankFour_holds
    _ 2 1 (CFSG.AGLEmbeddingD2.McLaughlin.Lie.statedClassicalModel_of_isOmegaEightPlus hO)
  rw [CFSG.SectionRank.pRank_quotient_eq _ hZ,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barM M L),
    pRank_barM_eq Nat.prime_three (by norm_num) M L hLM] at h4
  have hLM3 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hLM
  omega

theorem kFactBlockOneImageIrr3_of_griess (hG : GriessAllModelsStatement) :
    KFactBlockOneImageIrr3 := by
  intro G _ _ M S L hK hAsc hL h2 hsolv hM3 hOne E hEel hE9 hEP h9
  rcases isOmegaEightPlus_or_isFiveList hOne with hO | hF
  · exact (not_isOmegaEightPlus_of_pRank_le_three hG hL.le hL.perfect hM3 hO).elim
  · exact kFactBlockSixLieNoSwap_proved hG G M S L hK hAsc hL h2 hsolv hF E hEel hE9 hEP h9

end OneImageIrr

section Certified


theorem kFactBlockOneImageIrr3_holds : KFactBlockOneImageIrr3 :=
  OneImageIrr.kFactBlockOneImageIrr3_of_griess
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB
