module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreD2

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

namespace D2L2Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}

theorem pCore_ne_bot_of_components (h : D2L2Data p M H R X) (hD1 : D1For G) (hp5 : 5 ≤ p)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G)
    (hK : ∀ L : Subgroup G, IsTwoPrimeComponent M L → L ≤ H ⊓ M →
      barM M X ≤ Subgroup.centralizer (barM M L : Set _))
    (hB : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M X ≤ Subgroup.centralizer (barM M L : Set _)) :
    CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥ := by
  have hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M X ≤ Subgroup.centralizer (Lbar : Set _) := by
    intro Lbar hLbar
    obtain ⟨L, hL2, hbar, hL⟩ := h.pair.exists_weakSBlock_or_le_inf hLbar
    rw [← hbar]
    rcases hL with hblock | hle
    · exact hB L hblock
    · exact hK L hL2 hle
  have hle := h.le_pCore_of_forall_le_centralizer_components hD1 hp5 h84 hD2 hcomp
  intro hbot
  rw [hbot, le_bot_iff] at hle
  have hc := h.card_barM
  rw [hle, Subgroup.card_bot] at hc
  have := Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt
  omega

end D2L2Data

end CFSG.AGLEmbeddingD2
