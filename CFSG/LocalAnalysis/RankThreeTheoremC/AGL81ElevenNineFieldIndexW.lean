module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineFieldIndexOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineFieldAutOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding.ParabPrime Subgroup
open scoped commutatorElement

@[expose] def KFactBlockFieldIndexWAt (p : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), BlockL28Hyps M S L →
    pCoreOf 2 M ≤ S → (L.subgroupOf M).Normal →
    (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3) →
    p ∣ Nat.card (wPre (blockPL M S L)) →
    Open.pRank p (wPre (blockPL M S L)) ≤ 1 →
    ∀ a : ↥M ⧸ CFSG.pCore 2 ↥M, IsPGroup p (Subgroup.zpowers a) →
      a ∈ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (¬ ∃ v ∈ wPre (blockPL M S L), ∀ w ∈ wPre (blockPL M S L),
        ⁅a * v, w⁆ ∈ pCoreOf 2 (blockPL M S L)) →
      ∃ N : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), N.Normal ∧ N.index = p

variable {G : Type} [Group G] [Finite G]

theorem AGL81ElevenNineData.blockFieldIndexW_hyps (hS : Setting G) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hNX : NoXBlockFor G) (h98 : AGL81NineEightFour G) {p : ℕ}
    {P : Sylow p G} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    {L W : Subgroup G} {a₀ : G} (hd : AGL81ElevenNineData p P M H Q K L W a₀) :
    p.Prime ∧ p ≠ 2 ∧ BlockL28Hyps M (pCoreOf 2 H) L ∧ pCoreOf 2 M ≤ pCoreOf 2 H ∧
      (L.subgroupOf M).Normal ∧ (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3) ∧
      p ∣ Nat.card (wPre (blockPL M (pCoreOf 2 H) L)) ∧
      Open.pRank p (wPre (blockPL M (pCoreOf 2 H) L)) ≤ 1 ∧
      ∃ a : ↥M ⧸ CFSG.pCore 2 ↥M, IsPGroup p (Subgroup.zpowers a) ∧
        a ∈ Subgroup.normalizer (blockPL M (pCoreOf 2 H) L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        ¬ ∃ v ∈ wPre (blockPL M (pCoreOf 2 H) L), ∀ w ∈ wPre (blockPL M (pCoreOf 2 H) L),
          ⁅a * v, w⁆ ∈ pCoreOf 2 (blockPL M (pCoreOf 2 H) L) := by
  have hT := hd.data.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hX : ¬ NineThreeOne L := (hT.nineThree_not_one hK h85 hNX hd.block).1
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  obtain ⟨H₁, R₁, hesc⟩ := hd.data.escape
  have hp := hesc.prime
  set S := pCoreOf 2 H with hSdef
  have h93c := hT.nineThree hK h93 hd.block
  have ha₀HM := hd.sylow.2.1 hd.mem
  have ha₀S : a₀ ∈ Subgroup.normalizer (S : Set G) := hNH.symm ▸ ha₀HM.1
  have hinner : ∀ j ∈ jZero H L,
      (∀ y ∈ jZero H L, ⁅j⁻¹ * a₀, y⁆ ∈ pCoreOf 2 (jZero H L)) → False :=
    fun j hj hjy => hd.not_split (hd.split_of_inner hj hjy)
  have hLc : IsTwoPrimeComponent M L := hd.block.toIsTwoPrimeComponent
  have hXM : Subgroup.normalizer (S : Set G) ⊓ L ≤ M := by
    rw [hNH]
    exact inf_le_right.trans hLc.le
  have ha₀X : a₀ ∈ normalizer ((Subgroup.normalizer (S : Set G) ⊓ L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have h1 := mem_normalizer_iff.mp (le_normalizer ha₀S) y
    have h2 := mem_normalizer_iff.mp (hd.normal ha₀HM.2) y
    exact (mem_inf.trans (and_congr h1 h2)).trans mem_inf.symm
  have hnon : ¬ ∃ v ∈ wPre (blockPL M S L), ∀ w ∈ wPre (blockPL M S L),
      ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a₀, ha₀HM.2⟩ * v, w⁆ ∈
        pCoreOf 2 (blockPL M S L) := fun h => by
    obtain ⟨j, hj, hjy⟩ := exists_inner_jZero_of_inner_wPre hXM ha₀HM.2 ha₀X h
    rw [hNH] at hj hjy
    exact hinner j hj hjy
  have hdvd : p ∣ Nat.card (wPre (blockPL M S L)) := by
    refine dvd_card_wPre_of_dvd_jZero hXM hp hesc.ne_two ?_
    rw [hNH]
    exact hd.dvd
  have hrkW : Open.pRank p (wPre (blockPL M S L)) ≤ 1 := by
    refine (pRank_wPre_le_pRank_jZero hXM hp hesc.ne_two).trans ?_
    rw [hNH]
    exact hd.pRank_jZero_le_one
  have hyps : BlockL28Hyps M S L :=
    ⟨hK, hT.asc81bHyp, hd.block, h93c, hX, hT.not_isSylowTwoOf_inf hK h85 hNX hd.block⟩
  have hQS : pCoreOf 2 M ≤ S := (hd.data.nineEightFour' hS h98).2.1
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLc.le).mpr hd.normal
  have hLbM : barM M L ≤ barM M M := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hrk : ∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3 := by
    intro q hq hq2
    have h1 : Open.pRank q (barM M L) ≤ Open.pRank q (barM M M) :=
      CFSG.SectionRank.pRank_mono hq.one_lt hLbM
    have h2 := stmtBarPRankLift hq hq2 M M le_rfl
    have h3 := local_pRank_le_evenRank q hq hq2 M hesc.maxTwoLocal_M.1
    rw [hS.rank] at h3
    omega
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have haL' : mk ⟨a₀, ha₀HM.2⟩ ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    TenThreeThree.mem_normalizer_barM ha₀HM.2 (hd.normal ha₀HM.2)
  have haS' : mk ⟨a₀, ha₀HM.2⟩ ∈ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    TenThreeThree.mem_normalizer_barM ha₀HM.2 ha₀S
  have haJ : mk ⟨a₀, ha₀HM.2⟩ ∈
      Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.mem_normalizer_fintype
      (CFSG.HardMathSupport.Curtis.Coordinator.blockPL_conj_mem hT.asc81bHyp haL' haS')
  have hap : IsPGroup p (Subgroup.zpowers (mk ⟨a₀, ha₀HM.2⟩)) := by
    haveI : Fact p.Prime := ⟨hp⟩
    have h1 : (⟨a₀, ha₀HM.2⟩ : ↥M) ^ p ^ 1 = 1 := by
      rw [pow_one]
      exact Subtype.ext (by simp [← hd.order, pow_orderOf_eq_one])
    exact isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [← map_pow, h1, map_one])
  exact ⟨hp, hesc.ne_two, hyps, hQS, hLn, hrk, hdvd, hrkW, _, hap, haJ, hnon⟩

theorem agl81ElevenNineFieldAut_of_fieldIndexW
    (hFIW : ∀ p : ℕ, p.Prime → p ≠ 2 → KFactBlockFieldIndexWAt p) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hNX : NoXBlockFor G) (h98 : AGL81NineEightFour G) :
    AGL81ElevenNineFieldAut G := by
  intro hS p P M H Q K L W a₀ hd
  obtain ⟨hp, hp2, hyps, hQS, hLn, hrk, hdvd, hrkW, a, hap, haJ, hnon⟩ :=
    hd.blockFieldIndexW_hyps hS h85 h93 hNX h98
  obtain ⟨N, hNn, hNi⟩ := hFIW p hp hp2 G M _ L hyps hQS hLn hrk hdvd hrkW a hap haJ hnon
  exact hasNormalIndex_of_quotient hNn hNi

end CFSG.LocalAnalysis.RankThreeTheoremC
