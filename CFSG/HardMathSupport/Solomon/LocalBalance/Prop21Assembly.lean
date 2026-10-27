module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Input19DeltaReduction

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def LocalTwoBalanceGtFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProper G → ∀ p : ℕ, p.Prime → 5 < p →
    ∀ X : Subgroup G, X ≠ ⊤ → ∀ B : Subgroup G, B ≤ X → IsElemAbelian p B →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → 2 ≤ CFSG.Open.pRank p B →
      ∀ L : Subgroup G, GLAPComponent p X L → IsCompLocallyBalanced p 2 B L

theorem input19DeltaTwo_of_localBalance (hΔ : DeltaOfLocalBalance) (h2 : LocalTwoBalanceGtFive) :
    Input19DeltaTwo := by
  intro G _ _ hKP p hp hp5 B hB H hH hBH E hEB hE hcard
  have hBel : IsElemAbelian p B := hB.1
  have hrankB : CFSG.Open.pRank p B = GLATwoLocalRank p G := pRank_eq_of_card hp hBel hB.2.1
  have h2B : 2 ≤ CFSG.Open.pRank p B := by
    have h := CFSG.SectionRank.pRank_mono hp.one_lt hEB
    rwa [pRank_eq_of_card hp hE hcard] at h
  have hrank : GLATwoLocalRank p ↥H ≤ CFSG.Open.pRank p B :=
    hrankB ▸ glaTwoLocalRank_subgroup_le hp H
  exact hΔ G p hp (by omega) 2 (by norm_num) H B E hBH hBel ⟨hEB, hE, hcard⟩
    (h2 G hKP p hp hp5 H hH B hBH hBel hrank h2B)

theorem prop21_of_localBalance (hΔ : DeltaOfLocalBalance) (h3 : LocalThreeBalance)
    (h2 : LocalTwoBalanceGtFive) : Prop21 :=
  prop21_of_inputs (input19Delta_of_localBalance hΔ h3) (input19DeltaTwo_of_localBalance hΔ h2)

end CFSG.HardMathSupport.Solomon.LocalBalance
