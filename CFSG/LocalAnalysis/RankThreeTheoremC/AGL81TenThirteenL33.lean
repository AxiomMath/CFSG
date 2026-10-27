module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenBlock
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem false_of_l33u35l37he (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G) (h984 : AGL81NineEightFour G)
    (hB : KFactBlockNoL33U35L37He) (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {I₀ : Subgroup G} (hI₀ : I₀ ∈ cZero (H ⊓ L)) (hI : IsTwoPrimeComponent I₀ I₀)
    (hN : H ⊓ L ≤ normalizer (I₀ : Set G)) {U : Type} [Group U] [Finite U] [IsSimpleGroup U]
    (f : I₀ →* U) (hf : Function.Surjective f) (hU : IsL33U35L37HeOrder (Nat.card U)) :
    False := by
  classical
  obtain ⟨hK, hAsc, -, h93c, hX, hSyl⟩ := blockL28Hyps_of_cfg h85 h93 hD2 h984 hS hd hL
  have hM : I₀ ≤ M := hI₀.le.trans (inf_le_right.trans hL.le)
  have hbar : barM M I₀ ≤ blockParabolic M (pCoreOf 2 H) L :=
    barM_le_blockParabolic_of_cfg (L := L) (V := I₀) h984 hS hd hI₀.le
  have hbot : blockParabolic M (pCoreOf 2 H) L ≤
      Subgroup.normalizer ((⊥ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcop : Nat.Coprime 3 (Nat.card (⊥ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))) := by
    rw [Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hsup : blockParabolic M (pCoreOf 2 H) L ≤ Subgroup.normalizer
      (((barM M I₀ ⊔ ⊥) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) := by
    rw [sup_bot_eq]
    exact blockParabolic_le_normalizer_barM_of_cfg h984 hS hd hL.le hN
  exact hB G M (pCoreOf 2 H) L hK hAsc hL h93c hX hSyl
    (pRank_barM_le_three_of_cfg hS hd L) ⊥ I₀ hM bot_le hbar hbot hcop hsup hI.perfect
    U f hf hU

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
