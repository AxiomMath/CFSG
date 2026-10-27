module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.TRoute
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLie
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem isOmegaEightPlus_of_center_eq_bot {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    (h : WeakBlockModuleData.IsOmegaEightPlus (X ⧸ Subgroup.center X)) :
    WeakBlockModuleData.IsOmegaEightPlus X := by
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  exact ⟨d, hd, ⟨((QuotientGroup.quotientBot (G := X)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans e⟩⟩

theorem three_dvd_card_barM_of_two_le_pRank {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hLM : L ≤ M) (h : 2 ≤ Open.pRank 3 L) : 3 ∣ Nat.card (barM M L) := by
  apply three_dvd_card_of_two_le_pRank
  rw [pRank_barM_eq Nat.prime_three (by norm_num) M L hLM]
  exact h

theorem normal_twoGroup_eq_bot_barM {G : Type} [Group G] [Finite G] (M : Subgroup G) :
    ∀ N : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hNp
  have hle : N ≤ CFSG.pCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hN hNp
  rw [pCore_quotient_pCore_eq_bot' 2] at hle
  exact le_bot_iff.mp hle

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

end
