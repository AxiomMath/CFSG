module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedNext3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedNext3Heis
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Rank
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (D1Extremal D1Escape D1PhaseThree Asc81bEightFive Asc81bNineThree
  D1NoXBlock IsWeakSBlock KFactOutElemRank barM catalogSimpleSections_of_isKProper
  stmtBarPRankLift)

variable {G : Type} [Group G] [Finite G]

theorem d1ConstrainedWeakBlockGeFive_of_heisenberg (hK6 : KFactBlockHeisenbergAut)
    (hOut : KFactOutElemRank) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) : D1ConstrainedWeakBlockGeFive G := by
  intro hS p hp hp3 P M hM H hext hfact z hz hlayer Pbar zbar E C hEn e hdata hstr hcon hph hzP
    hCH huniq hNH T hTN hT2 hTidx hPT hST hchar L hL hPL hfaith hsyl hzL
  have hp5 : 5 ≤ p := by
    have h2 := hfact.out.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hfact.out (by norm_num)
    have := hext.ne_two
    omega
  have hyps : BlockL28Hyps M (pCoreOf 2 H) L :=
    ⟨hph.isKGroup.1, hph.asc81bHyp, hL, hph.nineThree h93 hL,
      (hph.nineThree_not_one h85 hD2 hL).1, hph.not_isSylowTwoOf_inf h85 hD2 hL⟩
  have hLbM : barM M L ≤ barM M M := by
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  have hrk : ∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3 := by
    intro q hq hq2
    have h1 : Open.pRank q (barM M L) ≤ Open.pRank q (barM M M) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono q hq.one_lt hLbM
    have h2 := stmtBarPRankLift hq hq2 M M le_rfl
    have h3 := local_pRank_le_localRank q hq.one_lt M hM.1.1
    have h4 := rankThreeLocalRank_le_evenRank (G := G) q hq hq2
    rw [hS.rank] at h4
    omega
  have hMtop : M ≠ ⊤ := fun hMt => hph.not_le (hMt ▸ le_top)
  have hcat : IsCatalogGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    ((catalogSimpleSections_of_isKProper hph.glob.kProper M hMtop).quotient
      _).isCatalogGroup_center_quotient hL.component
  have hpb := dvd_card_barM_of_faithful hOut hfact.out hp5 hz.pRank_eq hext.sylow_le hPL
    hL.component hcat hfaith
  have hQS : pCoreOf 2 M ≤ pCoreOf 2 H := hph.twoCore_M_le hph.twoCore_inf
  have hNS : Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) = H :=
    hext.toD1Escape.normalizer_twoCore_H
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) := by
    rw [hNS]
    exact hext.le_H
  have hidxL : ¬ p ∣ ((Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) ⊓ L).subgroupOf
      L).index := fun h =>
    hsyl (h.trans (Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono L
      (inf_le_inf_right L hPN))))
  obtain ⟨E₀, hEP, hEcard, hEexp, hEZ, -⟩ := hz.sl
  have hcard : Nat.card ↥(barM M E₀) = p ^ 3 :=
    (card_barM_of_faithful hEP hext.sylow_le hfaith).trans hEcard
  exact hK6 G M (pCoreOf 2 H) L hyps hQS hrk p hfact.out hp5 hpb
    (not_dvd_index_barM_of_not_dvd hL.le hidxL) (barM M E₀)
    (barM_le_normalizer hEP hext.sylow_le hPL) (barM_inf_centralizer_eq_bot hEP hfaith) hcard
    (pow_eq_one_of_mem_barM hEexp)
    (exists_noncomm_barM hEP hext.sylow_le hfaith
      (exists_noncomm_of_center hfact.out.two_le hz.orderOf_eq hEcard hEZ))

theorem d1ConstrainedWeakBlockResidue3_of_kfacts (hK4 : KFactBlockPerfectCoreThree)
    (hK5 : KFactBlockSylowThreeAut) (hK6 : KFactBlockHeisenbergAut) (hOut : KFactOutElemRank)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) :
    D1ConstrainedWeakBlockResidue3 G :=
  d1ConstrainedWeakBlockResidue3_of_five hK4 hK5 hOut h85 h93 hD2
    (d1ConstrainedWeakBlockGeFive_of_heisenberg hK6 hOut h85 h93 hD2)

end CFSG.LocalAnalysis.RankThreeTheoremC
