module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Ctx

public section

open Subgroup

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem fr_keyF (hG : FrobGlobal G) (hl : FrobLocal p P M x) {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) {D : Subgroup G} (hD : IsPGroup r D) (hDM : D ≤ M)
    (hD4 : 4 ≤ CFSG.Open.pRank r D) (hLD : layerOf x ≤ normalizer (D : Set G)) : False := by
  have hr : r.Prime := Fact.out
  have hpos : 0 < CFSG.Open.pRank r D := by omega
  have hdvd : r ∣ Nat.card G :=
    CFSG.PreuniquenessRankFour.Helpers.prime_dvd_card_of_positive_rank r hr D hpos
  have hrankM : 4 ≤ CFSG.Open.pRank r M :=
    hD4.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono r hr hDM)
  have hrankG : 4 ≤ CFSG.Open.GLBTwoLocalRank r G :=
    hrankM.trans (le_csSup (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove r hr)
      ⟨M, hl.loc.maxLocal.1, rfl⟩)
  have hβ : r ∈ CFSG.Open.GLBBetaFour G := ⟨hr, hr2, hdvd, hrankG⟩
  obtain ⟨F, hDF⟩ := hD.exists_le_sylow
  have hF3 : 3 ≤ CFSG.Open.pRank r (F : Subgroup G) := by
    have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono r hr hDF
    omega
  obtain ⟨H, hHloc, hcoreH⟩ := (hG.pre r hβ).2 F
  obtain ⟨M', hHM', hM'max⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.exists_maximal_twoLocal hHloc
  have hcoreM' : CFSG.Open.GLBWeakCore r (F : Subgroup G) ≤ M' := hcoreH.trans hHM'
  have hFM' : (F : Subgroup G) ≤ M' :=
    (CFSG.PreuniquenessRankFour.Helpers.subgroup_le_weakCore_of_rank r hr
      (F : Subgroup G) hF3).trans hcoreM'
  have hDM' : D ≤ M' := hDF.trans hFM'
  have h3 : 3 ≤ CFSG.Open.pRank r (M ⊓ M') := by
    have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono r hr (le_inf hDM hDM')
    omega
  have hMM' : M ≤ M' := hG.d1 r hβ F M' hM'max hcoreM' M hl.loc.maxLocal.1 h3
  have hM'M : M' = M := hl.loc.maxLocal.2 M' hM'max.1 hMM'
  have hcoreM : CFSG.Open.GLBWeakCore r (F : Subgroup G) ≤ M :=
    hcoreH.trans (hHM'.trans hM'M.le)
  have hsup : CFSG.Open.pRank r D ≤
      CFSG.Open.pRank r (D ⊔ ((F : Subgroup G) ⊓ Subgroup.centralizer (D : Set G))) :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_mono r hr le_sup_left
  have hN : Subgroup.normalizer (D : Set G) ≤ CFSG.Open.GLBWeakCore r (F : Subgroup G) :=
    CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore r hDF (by omega) (by omega)
  have hNM : Subgroup.normalizer (D : Set G) ≤ M := hN.trans hcoreM
  exact hl.not_le (hLD.trans hNM)

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
