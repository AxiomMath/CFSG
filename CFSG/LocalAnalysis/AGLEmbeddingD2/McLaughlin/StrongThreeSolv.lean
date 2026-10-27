module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PerfectCore
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig
import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding

@[expose] def KFactStrongThreeSolv : Prop :=
  ∀ (N : Type) [Group N] [Finite N], Open.IsKGroup N → ∀ N₀ : Subgroup N,
    GLBStronglyEmbedded 3 N₀ → 2 ≤ Open.pRank 3 N₀ →
    ∀ Y : Subgroup N, Y ≤ N₀ → ⁅Y, Y⁆ = Y → ¬ 3 ∣ Nat.card Y

variable {G : Type} [Group G] [Finite G]

theorem d2PerfectThreePrime_of_strongly (hK : KFactStrongThreeSolv) (hKP : IsKProper G)
    {M N : Subgroup G} (hN : N ≠ ⊤) (hstr : GLBStronglyEmbedded 3 ((N ⊓ M).subgroupOf N))
    (h2 : 2 ≤ Open.pRank 3 (N ⊓ M)) : D2PerfectThreePrime N M := by
  intro Y hY hYp h3
  have hKN : Open.IsKGroup ↥N :=
    isKGroup_of_catalogSimpleSections (catalogSimpleSections_of_isKProper hKP N hN)
  have hYN : Y ≤ N := hY.trans inf_le_left
  refine hK ↥N hKN ((N ⊓ M).subgroupOf N) hstr ?_ (Y.subgroupOf N)
    (fun y hy => Subgroup.mem_subgroupOf.mpr (hY (Subgroup.mem_subgroupOf.mp hy))) ?_ ?_
  · rw [CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three _ _
      inf_le_left]
    exact h2
  · apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYN, hYp]
  · rwa [← Subgroup.card_map_of_injective N.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hYN]

end CFSG.AGLEmbeddingD2.McLaughlin
