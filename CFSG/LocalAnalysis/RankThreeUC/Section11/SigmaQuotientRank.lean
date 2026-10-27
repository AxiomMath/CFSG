module




public import CFSG.LocalAnalysis.RankThreeUC.Section11.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section12.NonRankOneNormalizerOddRank
public import CFSG.LocalAnalysis.RankThreeUC.SubgroupCentralizerQuotientRank.SubgroupCentralizerQuotientRank
public import CFSG.LocalAnalysis.RankThreeUC.Section12.NonTISmallQuotient
public import CFSG.LocalAnalysis.RankThreeUC.Section12.NonTIFrattiniQuotient.NonTIFrattiniQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section11

namespace SigmaQuotientRank

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem sigma_quotient_rank {M T V₀ V : Subgroup G} (h : Setting G M T V₀ V)
    {p : ℕ} (hp : p ∈ SourceSetting.sigmaOf G M) {X : Subgroup G} (hXp : IsPGroup p X) (hXM : X ≤ M) :
    ∃ _ : ((X ⊓ centralizer (V₀ : Set G)).subgroupOf X).Normal,
      CFSG.Assembly.pRank p
        (⊤ : Subgroup (↥X ⧸ (X ⊓ centralizer (V₀ : Set G)).subgroupOf X)) ≤ 1 := by
  obtain ⟨hpp, hp2, -⟩ := Section12.NonTISigmaPrimeRank.sigma_prime_rank hp
  have hsub : (X ⊓ centralizer (V₀ : Set G)).subgroupOf X = centralizerInSubgroup X V₀ := by
    unfold centralizerInSubgroup
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hnX : X ≤ normalizer (V₀ : Set G) := by
    rcases h.moduleChoice with hm | ⟨-, h0⟩
    · have h1 := hm.1
      exact hXM.trans (mem_normalElemAbelian2.mp h1).2.2.2
    · subst h0
      intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp
  have hker := Section12.NonTISmallQuotient.conjAction_ker X V₀ hnX
  haveI hNX : (centralizerInSubgroup X V₀).Normal := hker ▸ MonoidHom.normal_ker _
  have hN : ((X ⊓ centralizer (V₀ : Set G)).subgroupOf X).Normal := by
    rw [hsub]; exact hNX
  refine ⟨hN, ?_⟩
  suffices hq0 : CFSG.pRank p (↥X ⧸ centralizerInSubgroup X V₀) ≤ 1 by
    have hq : CFSG.pRank p (↥X ⧸ (X ⊓ centralizer (V₀ : Set G)).subgroupOf X) ≤ 1 := by
      have key : ∀ (N : Subgroup X) [N.Normal], N = centralizerInSubgroup X V₀ →
          CFSG.pRank p (↥X ⧸ N) ≤ 1 := by
        rintro N _ rfl
        exact hq0
      exact key _ hsub
    show CFSG.Open.pRank p _ ≤ 1
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hq
  by_cases h0 : V₀ = ⊥
  · subst h0
    have htop : centralizerInSubgroup X ⊥ = ⊤ := by
      ext x
      simp [centralizerInSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    haveI : Subsingleton (↥X ⧸ centralizerInSubgroup X (⊥ : Subgroup G)) := by
      constructor
      intro a b
      induction a using QuotientGroup.induction_on
      induction b using QuotientGroup.induction_on
      rw [QuotientGroup.eq]
      rw [htop]; trivial
    exact OddRankOneQuotient.pRank_le_one_of_sylow_cyclic hpp fun P => inferInstance
  · have hV0 : V₀ ∈ normalElemAbelian2 M := by
      rcases h.moduleChoice with hm | ⟨-, h0'⟩
      · exact hm.1
      · exact absurd h0' h0
    have hnM : M ≤ normalizer (V₀ : Set G) := (mem_normalElemAbelian2.mp hV0).2.2.2
    haveI hNM : (centralizerInSubgroup M V₀).Normal := by
      rw [← Section12.NonTISmallQuotient.conjAction_ker M V₀ hnM]
      exact MonoidHom.normal_ker _
    have hc12 : Section12.Context G M T :=
      ⟨h.context.uc, h.context.mSigma, h.context.sylow⟩
    have hM : CFSG.pRank p (↥M ⧸ centralizerInSubgroup M V₀) ≤ 1 := by
      by_cases h3 : CFSG.Assembly.pRank 2 V₀ ≤ 3
      · exact Section12.NonTISmallQuotient.quotient_rank_le_of_small hV0 h3 hpp hp2
      · push Not at h3
        have hnot := h.not_V1 (by omega)
        exact Section12.NonTIFrattiniQuotient.quotient_rank_le_of_normalizer
          hc12 hV0 hp
          (Section12.NonRankOneNormalizerOddRank.pRank_normalizerCentralizerIn_le_one
            hc12 hV0 hp hnot)
    exact le_trans (SubgroupCentralizerQuotientRank.pRank_quotient_le hXM hpp.one_lt) hM

end SigmaQuotientRank

end Section11

end CFSG.LocalAnalysis.RankThreeUC
