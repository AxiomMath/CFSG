module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeCover
import CFSG.Adapters.LinearCatalogStated
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open TauCeti
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaOver)

theorem kGroupLowRank24_12_three_of_cross_simple
    (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    {X : Type} [Group X] [Finite X]
    {K E : Subgroup X} (hKq : CFSG.IsQuasisimple ↥K) (hKcat : CFSG.SectionRank.IsKGroupCat ↥K)
    (hKn : K.Normal) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2)
    (hrk : CFSG.Open.pRank 3 (K ⊔ E) ≤ 3) (hΓ : ¬ K ≤ gammaOver 1 3 E K)
    {d : ValidLieTypeIndex} (hpd : 3 ≠ d.1.characteristic)
    (φ : ↥K ≃* (CFSGIndex.lie d).Group) : KGroupLowRank24_12 3 ↥K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrkK : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) le_sup_left).trans hrk
  by_cases hexc : CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1
  · refine ⟨Nat.prime_three, by norm_num, hKq, hKcat, ?_⟩
    obtain ⟨d, hv⟩ := d
    rcases hexc with ⟨-, h⟩ | ⟨h5, -⟩
    · rcases h with ⟨q, hq2, hq3, rfl⟩ | ⟨q, hq2, hq3, rfl⟩ | ⟨q, hq2, hq1, rfl⟩ |
        ⟨q, hq2, hq1, rfl | rfl⟩ | rfl
      ·
        have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv φ
        rw [hq2, hq3] at hm
        refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
        exact Or.inl hm
      ·
        have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv φ
        rw [hq2, hq3] at hm
        refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
        exact Or.inr (Or.inl hm)
      ·
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv φ
        rw [hq2, hq1] at hm
        left
        iterate 8 right
        exact CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two hm
      ·
        have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hq2
          (by norm_num) φ
        rw [hq2, hq1] at hm
        refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
        exact Or.inr (Or.inr (Or.inl hm))
      ·
        exfalso
        have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 4 q hv hq2
          (by norm_num) φ
        rw [hq2, hq1] at hm
        obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hm
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have : CharP F 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hF
        have h4 := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedProj_sp
          (K := F) (n := 4) Nat.prime_three (by rw [hF]; norm_num)
        rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h4
        omega
      ·
        refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
        iterate 4 right
        left
        exact CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv φ
    · omega
  · exact absurd (le_gammaOver_of_seitz hS Nat.prime_three (by norm_num) hKn hpd hexc φ hE hEc)
      hΓ

theorem kGroupLowRank24_12_three_of_cross
    (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) (hGA : CFSG.Open.GriessAllModelsStatement)
    (hD : CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover.TwE6ThreeOpenDiag)
    (hCR : CrossCoverResidual24_12Three)
    {X : Type} [Group X] [Finite X] {K E : Subgroup X} (hKq : CFSG.IsQuasisimple ↥K)
    (hOp : CFSG.pPrimeCore 3 ↥K = ⊥) (hKcat : CFSG.SectionRank.IsKGroupCat ↥K) (hKn : K.Normal)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2) (hrk : CFSG.Open.pRank 3 (K ⊔ E) ≤ 3)
    (hΓ : ¬ K ≤ gammaOver 1 3 E K) {d : ValidLieTypeIndex} (hpd : 3 ≠ d.1.characteristic)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (CFSGIndex.lie d).Group) : KGroupLowRank24_12 3 ↥K := by
  by_cases hZ : Subgroup.center ↥K = ⊥
  · exact kGroupLowRank24_12_three_of_cross_simple hS hKq hKcat hKn hE hEc hrk hΓ hpd
      (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e)
  · exact kGroupLowRank24_12_three_of_cross_cover hGA hD hCR hKq hOp hKcat hKn hE hEc hrk hΓ
      hpd e hZ

end CFSG.LocalAnalysis.AGL81I.Section3
