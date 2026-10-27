module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySeven

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def AGL81TenTenCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    p ∈ rankThreeSigmaA G → AGL81CfgData p P M H Q K →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ¬ (L.subgroupOf M).Normal →
      p = 3 ∧ IsAltTwoP 3 K ∧ ∀ I₀ ∈ cZero (H ⊓ L),
        CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ hyp111Pre p H K

theorem agl81ElevenSixCfg_of (h1010 : AGL81TenTenCfg G) (h91 : AGL81TenNineOneCfg G)
    (h10C : AGL81TenOneCZero G) : AGL81ElevenSixCfg G := by
  intro hS p P M H Q K hσ hd _ L hL
  by_cases hN : (L.subgroupOf M).Normal
  · exact Or.inl hN
  · obtain ⟨hp3, hA, hall⟩ := h1010 hS p P M H Q K hσ hd L hL hN
    obtain ⟨I₀, hI₀⟩ := h10C hS p P M H Q K hd L hL (h91 hS p P M H Q K hd L hL)
    exact Or.inr ⟨hp3, hA, I₀, hI₀, hall I₀ hI₀⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
