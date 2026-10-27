module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLie
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineFieldIndexWDispatch
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.QuasithinUnique Subgroup

@[expose] def KFactTenElevenOneLieCl : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → Open.IsQuasisimple ↥L →
    CFSG.pCore 2 Y = ⊥ → IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) →
    (∃ T J : Subgroup (↥L ⧸ Subgroup.center ↥L), IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set _) ≤ J ∧ J ≠ Subgroup.normalizer (T : Set _) ∧ J ≠ ⊤) →
    Open.pRank 3 (⊤ : Subgroup Y) = 3 →
    (∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      Open.pRank 3 (Subgroup.centralizer (E : Set Y)) ≤ 2) →
    (∃ N : Subgroup Y, N.Normal ∧ N.index = 3) →
    ∃ e : ℕ, IsLieOver (↥L ⧸ Subgroup.center ↥L) (.A 2) 2 e

variable {G : Type} [Group G] [Finite G]

open TenElevenOneLie in
theorem AGL81ElevenNineData.lie_of_not_centRankThreeAt_cl (hKF : KFactTenElevenOneLieCl)
    (hS : Setting G) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hNX : NoXBlockFor G)
    (h98 : AGL81NineEightFour G) {P : Sylow 3 G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {L W : Subgroup G} {a₀ : G}
    (hd : AGL81ElevenNineData 3 P M H Q K L W a₀) (hc : ¬ CentRankThreeAt 3 M)
    (hNI : HasNormalIndex M 3) :
    ∃ e : ℕ, IsLieOver (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) (.A 2) 2 e := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hp, hp2, hyps, -, -, hrk, hdvd, hrkW, a, hap, haJ, hnon⟩ :=
    hd.blockFieldIndexW_hyps hS h85 h93 hNX h98
  have h2 := nineThreeTwo_of_not_inner_wPre hp hp2 hyps hrk hdvd hrkW hap haJ hnon
  obtain ⟨-, hA, hblock, -, -, hSy⟩ := hyps
  obtain ⟨hcl, T, J, hT2, hle, hne, htop, -⟩ := BlockCyc.nineThreeTwo_parabolic hA hblock hSy h2
  have hLn : (barM M L).Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hd.block.le).mpr hd.normal).map _
      (QuotientGroup.mk'_surjective _)
  have hrank : Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) = 3 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥M) (not_three_dvd_card_pCore_two ↥M),
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup M]
    obtain ⟨H₁, R₁, hesc⟩ := hd.data.escape
    refine le_antisymm ?_ (hesc.three_le_pRank.trans
      (CFSG.SectionRank.pRank_mono (by norm_num) hesc.le_M))
    have h1 := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) M hesc.maxTwoLocal_M.1
    rw [hS.rank] at h1
    exact h1
  exact hKF _ (barM M L) hLn hd.block.component.2.2 (pCore_quotient_pCore_eq_bot' 2) hcl
    ⟨T, J, hT2, hle, hne, htop⟩ hrank (exists_bar_of_not_centRankThreeAt hc)
    (exists_bar_normal_index hNI)

theorem agl81TenElevenOneDisc_of_lieCl (hKF : KFactTenElevenOneLieCl) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hNX : NoXBlockFor G) (h98 : AGL81NineEightFour G)
    (h : AGL81TenElevenOneLie G) : AGL81TenElevenOneDisc G :=
  fun hS P M H Q K L W a₀ hd V hVM hc hNI => h hS P M H Q K L W a₀ hd V hVM hc hNI
    (hd.lie_of_not_centRankThreeAt_cl hKF hS h85 h93 hNX h98 hc hNI)

end CFSG.LocalAnalysis.RankThreeTheoremC
