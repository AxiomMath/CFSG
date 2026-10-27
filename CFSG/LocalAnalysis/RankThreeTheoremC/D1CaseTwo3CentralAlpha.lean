module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralDefs
import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterMain
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralAxis
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralU

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open CFSG.HardMathSupport.Curtis.Coordinator
open scoped commutatorElement

theorem false_of_sylow_le_commutator_of_index_prime {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (T : Sylow p Y) (hT : (T : Subgroup Y) ≤ commutator Y) {N : Subgroup Y}
    [N.Normal] (hN : N.index = p) : False := by
  have hcard : Nat.card (Y ⧸ N) = p := hN
  have : IsCyclic (Y ⧸ N) := isCyclic_of_prime_card hcard
  have hcomm : commutator Y ≤ N := by
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    have h1 : QuotientGroup.mk' N ⁅g₁, g₂⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (isMulCommutative_iff.mp (inferInstance : IsMulCommutative (Y ⧸ N)) _ _)
    exact (QuotientGroup.eq_one_iff _).mp h1
  have h1 : N.index ∣ (T : Subgroup Y).index := Subgroup.index_dvd_of_le (hT.trans hcomm)
  rw [hN] at h1
  exact T.not_dvd_index h1

variable {G : Type} [Group G] [Finite G]

theorem D1CaseTwoDataU.false_of_alpha (hKF : KFactBlockFieldIndex)
    (hOut : KFactOutCyclic) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (hSch : KFactCatalogSchreier) (hGrp : CaseTwoGroupFacts) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    {P : Sylow 3 G} {M H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hd : D1CaseTwoDataU 3 P M H R Rbar) {z : H} (hz : D1CaseTwoCand 3 M H R z)
    (hRP : R = (P : Subgroup G)) (hα : D1CaseTwoAlpha 3 P M H) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hph : D1PhaseThree 3 P M H R := hd.toPhaseThree hOut hS hKL
  have hcomm := hd.sylow_le_commutator hOut hS hGrp hz hRP
  obtain ⟨L, hL, hLn, hV3, a, haP, hnon⟩ := hα
  obtain ⟨Kb, hKb, hKX, -⟩ := hz
  set S := pCoreOf 2 H with hSdef
  have hyps : BlockL28Hyps M S L :=
    ⟨hph.isKGroup.1, hph.asc81bHyp, hL, hph.nineThree h93 hL,
      (hph.nineThree_not_one h85 hD2 hL).1, hph.not_isSylowTwoOf_inf h85 hD2 hL⟩
  have hQS : pCoreOf 2 M ≤ S := hph.twoCore_M_le hph.twoCore_inf
  have hLbM : barM M L ≤ barM M M := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hrk : ∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3 := by
    intro q hq hq2
    have h1 : Open.pRank q (barM M L) ≤ Open.pRank q (barM M M) :=
      pRank_mono q hq.one_lt hLbM
    have h2 := stmtBarPRankLift hq hq2 M M le_rfl
    have h3 := local_pRank_le_evenRank q hq hq2 M hd.cfg.loc.isCoreMaxLocal.1.1
    have h4 := hd.cfg.glob.rank
    omega
  have hLc : IsTwoPrimeComponent M L := hL.toIsTwoPrimeComponent
  have hKeq := hph.toD1Escape.inf_eq_inf_normalizer_twoCore
  have hNL : Subgroup.normalizer (S : Set G) ⊓ L ≤ H ⊓ M := by
    intro x hx
    rw [hKeq]
    exact ⟨hLc.le hx.2, hx.1⟩
  have hJHM : blockPL M S L ≤ barM M (H ⊓ M) := barM_mono hNL
  have hV1 : Open.pRank 3 (perfectJoin (blockPL M S L)) ≤ 1 :=
    hd.pRank_le_one_of_perfect_barM hOut hS hKL hSch hKb hKX
      ((perfectJoin_le _).trans hJHM) (perfectJoin_perfect _)
  have hPM : (P : Subgroup G) ≤ M := hd.cfg.ext.sylow_le
  have haH : (a : G) ∈ H := hd.cfg.ext.le_H (hRP ▸ haP)
  have haL : (a : G) ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLc.le).mp hLn a.2
  have haS : (a : G) ∈ Subgroup.normalizer (S : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 H haH
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have haL' : mk a ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM a.2 haL
  have haS' : mk a ∈ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM a.2 haS
  have haJ : mk a ∈ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.mem_normalizer_fintype (blockPL_conj_mem hph.asc81bHyp haL' haS')
  have ha3 : IsPGroup 3 (Subgroup.zpowers (mk a)) := by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨(a : G), haP⟩
    have h1 : a ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    exact CFSG.AGLEmbedding.isPGroup_zpowers_of_pow_eq_one (k := k)
      (by rw [← map_pow, h1, map_one])
  obtain ⟨N, hNn, hNi⟩ := hKF G M S L hyps hQS hLn hrk hV3 hV1 (mk a) ha3 haJ hnon
  have := hNn
  let Pbar : Sylow 3 (↥M ⧸ CFSG.pCore 2 ↥M) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M)) (P.subtype hPM)
  have hcommM : ∀ x : ↥M, (x : G) ∈ ⁅M, M⁆ → x ∈ commutator ↥M := by
    intro x hx
    have h1 := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥M)) (H₂ := (⊤ : Subgroup ↥M))
      M.subtype
    rw [Subgroup.map_top, Subgroup.range_subtype] at h1
    have hx' : (x : G) ∈ (commutator ↥M).map M.subtype := h1 ▸ hx
    obtain ⟨y, hy, hyx⟩ := hx'
    exact M.subtype_injective hyx ▸ hy
  have hPc : (Pbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ commutator (↥M ⧸ CFSG.pCore 2 ↥M) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥M)) (H₂ := (⊤ : Subgroup ↥M))
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h1
    have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
      (hcommM x (hcomm hx))
    rw [commutator, h1] at hmem
    exact hmem
  exact false_of_sylow_le_commutator_of_index_prime Pbar hPc hNi

theorem d1CaseTwoCentral3_of_beta (hk : D1CaseTwoKFacts3 G) (hgrp : CaseTwoGroupFacts)
    (hKF : KFactBlockFieldIndex) (h : D1CaseTwoCentral3Beta G) : D1CaseTwoCentral3 G := by
  intro p P M H R Rbar hcfg hcyc z hz hcen
  by_cases hα : p = 3 ∧ R = (P : Subgroup G) ∧ D1CaseTwoAlpha p P M H
  · obtain ⟨rfl, hRP, hα⟩ := hα
    exact D1CaseTwoDataU.false_of_alpha hKF hk.out hk.seitzCyc hk.caseTwoLocal hk.schreier hgrp
      hk.eightFive hk.nineThree hk.noXBlock ⟨hcfg, hcyc⟩ hz hRP hα
  · exact h p P M H R Rbar hcfg hcyc z hz hcen hα

theorem d1CaseTwoCentral3Beta_of_central3 (h : D1CaseTwoCentral3 G) : D1CaseTwoCentral3Beta G :=
  fun p P M H R Rbar hcfg hcyc z hz hcen _ => h p P M H R Rbar hcfg hcyc z hz hcen

end CFSG.LocalAnalysis.RankThreeTheoremC
