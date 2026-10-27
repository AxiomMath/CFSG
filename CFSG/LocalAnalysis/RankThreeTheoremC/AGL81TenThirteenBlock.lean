module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem blockL28Hyps_of_cfg (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G) (h984 : AGL81NineEightFour G) (hS : Setting G)
    (hd : AGL81CfgData p P M H Q K) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    BlockL28Hyps M (pCoreOf 2 H) L := by
  have hT := hd.toTwoLocalPhaseThree' hS h984
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  exact ⟨hK, hT.asc81bHyp, hL, hT.nineThree hK h93 hL,
    (hT.nineThree_not_one hK h85 hD2 hL).1, hT.not_isSylowTwoOf_inf hK h85 hD2 hL⟩

theorem blockInnerHyp_of_cfg (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G) (h984 : AGL81NineEightFour G) (hS : Setting G)
    (hd : AGL81CfgData p P M H Q K) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    BlockInnerHyp M (pCoreOf 2 H) L := by
  have hT := hd.toTwoLocalPhaseThree' hS h984
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  intro l hl hlS
  exact hT.blockInnerNormalizer hK h84 h86 hD2 hL l hl hlS

theorem pRank_barM_le_three_of_cfg (hS : Setting G) (hd : AGL81CfgData p P M H Q K)
    (L : Subgroup G) : ∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3 := by
  intro q hq hq2
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hLbM : barM M L ≤ barM M M := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have h1 := CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono q hq.one_lt hLbM
  have h2 := stmtBarPRankLift hq hq2 M M le_rfl
  have h3 := local_pRank_le_evenRank q hq hq2 M hesc.maxTwoLocal_M.1
  rw [hS.rank] at h3
  omega

theorem blockParabolic_eq_of_cfg (h984 : AGL81NineEightFour G) (hS : Setting G)
    (hd : AGL81CfgData p P M H Q K) (L : Subgroup G) :
    blockParabolic M (pCoreOf 2 H) L = barM M (H ⊓ L) := by
  have hT := hd.toTwoLocalPhaseThree' hS h984
  show barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) = barM M (H ⊓ L)
  rw [hT.toTwoLocalPair.normalizer_twoCore_H]

theorem card_blockParabolic_dvd_of_cfg (h984 : AGL81NineEightFour G) (hS : Setting G)
    (hd : AGL81CfgData p P M H Q K) {L : Subgroup G} (hLM : L ≤ M) :
    Nat.card (blockParabolic M (pCoreOf 2 H) L) ∣ Nat.card H := by
  rw [blockParabolic_eq_of_cfg h984 hS hd L]
  show Nat.card (((H ⊓ L).subgroupOf M).map
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) ∣ Nat.card H
  refine (Subgroup.card_map_dvd (H := (H ⊓ L).subgroupOf M)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).trans ?_
  have hle : ((H ⊓ L).subgroupOf M).map M.subtype ≤ H ⊓ L := by
    rintro x ⟨m, hm, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hm
  have h1 : Nat.card (((H ⊓ L).subgroupOf M).map M.subtype) ∣ Nat.card ↥(H ⊓ L) :=
    Subgroup.card_dvd_of_le hle
  have h2 : Nat.card ↥(H ⊓ L) ∣ Nat.card H :=
    Subgroup.card_dvd_of_le (inf_le_left : H ⊓ L ≤ H)
  rw [← Subgroup.card_subtype M ((H ⊓ L).subgroupOf M)]
  exact h1.trans h2

theorem barM_le_blockParabolic_of_cfg (h984 : AGL81NineEightFour G) (hS : Setting G)
    (hd : AGL81CfgData p P M H Q K) {L V : Subgroup G} (hV : V ≤ H ⊓ L) :
    barM M V ≤ blockParabolic M (pCoreOf 2 H) L := by
  rw [blockParabolic_eq_of_cfg h984 hS hd L]
  exact barM_mono hV

theorem blockParabolic_le_normalizer_barM_of_cfg (h984 : AGL81NineEightFour G) (hS : Setting G)
    (hd : AGL81CfgData p P M H Q K) {L V : Subgroup G} (hLM : L ≤ M)
    (hN : H ⊓ L ≤ normalizer (V : Set G)) :
    blockParabolic M (pCoreOf 2 H) L ≤
      normalizer (barM M V : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  rw [blockParabolic_eq_of_cfg h984 hS hd L]
  rintro x ⟨m, hm, rfl⟩
  exact mem_normalizer_barM m.2 (hN (Subgroup.mem_subgroupOf.mp hm))

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
