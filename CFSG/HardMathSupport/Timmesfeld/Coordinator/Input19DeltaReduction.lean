module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.TwoLocalTools
public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def DeltaOfLocalBalance : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ k : ℕ, 1 ≤ k →
    ∀ H B E : Subgroup G, B ≤ H → IsElemAbelian p B → IsEkIn p k B E →
      (∀ L : Subgroup G, GLAPComponent p H L → IsCompLocallyBalanced p k B L) →
      (⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
        GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({e} : Set G))) ≤ GLAPPrimeCoreOf p H

@[expose] def LocalThreeBalance : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProper G → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ X : Subgroup G, X ≠ ⊤ → ∀ B : Subgroup G, B ≤ X → IsElemAbelian p B →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → 3 ≤ CFSG.Open.pRank p B →
      ∀ L : Subgroup G, GLAPComponent p X L → IsCompLocallyBalanced p 3 B L

theorem input19Delta_of_localBalance (hΔ : DeltaOfLocalBalance) (h3 : LocalThreeBalance) :
    Input19Delta := by
  intro G _ _ hKP p hp hp2 B hB H hH hBH E hEB hE hcard
  have hBel : IsElemAbelian p B := hB.1
  have hrankB : CFSG.Open.pRank p B = GLATwoLocalRank p G := pRank_eq_of_card hp hBel hB.2.1
  have h3B : 3 ≤ CFSG.Open.pRank p B := by
    have h := CFSG.SectionRank.pRank_mono hp.one_lt hEB
    rwa [pRank_eq_of_card hp hE hcard] at h
  have hrank : GLATwoLocalRank p ↥H ≤ CFSG.Open.pRank p B :=
    hrankB ▸ glaTwoLocalRank_subgroup_le hp H
  exact hΔ G p hp hp2 3 (by norm_num) H B E hBH hBel ⟨hEB, hE, hcard⟩
    (h3 G hKP p hp hp2 H hH B hBH hBel hrank h3B)

end CFSG.HardMathSupport.Timmesfeld.Coordinator
