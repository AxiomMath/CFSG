module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSixCfgOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81TenTenNotXCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ¬ (L.subgroupOf M).Normal → ∀ I₀ ∈ cZero (H ⊓ L),
      ¬ CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ d1PlusCore p H K

variable {G}

theorem agl81TenTenCfg_of (hnx : AGL81TenTenNotXCfg G) (h1013 : AGL81TenThirteenAt G)
    (h91 : AGL81TenNineOneCfg G) (h10C : AGL81TenOneCZero G) : AGL81TenTenCfg G := by
  intro hS p P M H Q K hσ hd L hL hN
  have hI : ∀ I₀ ∈ cZero (H ⊓ L), p = 3 ∧ IsAltTwoP 3 K ∧
      CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ hyp111Pre p H K := fun I₀ hI₀ =>
    (h1013 hS p P M H Q K hσ hd L hL I₀ hI₀).resolve_left
      (hnx hS p P M H Q K hd L hL hN I₀ hI₀)
  obtain ⟨I₀, hI₀⟩ := h10C hS p P M H Q K hd L hL (h91 hS p P M H Q K hd L hL)
  obtain ⟨hp, hA, -⟩ := hI I₀ hI₀
  exact ⟨hp, hA, fun I₁ hI₁ => (hI I₁ hI₁).2.2⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
