module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Data

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}

theorem D2Escape.survivorData_of_reduced [Fact p.Prime] (h : D2Escape p P M A H R)
    (hglob : AGLGlobal G)
    (hD : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) →
      W = ⊥ ∨ (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ W)
    (hC : ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer ((A.subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
            Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) :
    AGLSurvivorData p M H R A := by
  have hAH : A ≤ H := h.A_le.trans h.le_H
  have hAp : IsPGroup p A := h.isPGroup.to_le h.A_le
  have hA1 : A ≠ ⊥ := by
    intro hbot
    have hc := h.card_A
    rw [hbot, Subgroup.card_bot] at hc
    have := Nat.one_lt_pow two_ne_zero h.prime.one_lt
    omega
  have hAbar : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≠ ⊥ := by
    intro hbot
    apply hA1
    have hc := h.card_map_eq h.A_le
    rw [hbot, Subgroup.card_bot] at hc
    exact Subgroup.eq_bot_of_card_eq A hc.symm
  have hU : primeComplementCore (G := ((((H ⊓ M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) : Type _)) p = ⊥ :=
    primeComplementCore_eq_bot_of_dichotomy hD (hAp.comap_subtype.map _) hAbar
  have hpair : AGLPair p M H R :=
    h.toPair hglob (h.twoCore_inf_eq_of_primeCore_inf_eq (h.primeCore_inf_eq_iff.mpr hU))
  exact ⟨hpair, h.A_le, hA1,
    fun _ hY hYN => le_glbPrimeCore_or_le_of_forall h.primeCore_le hAH hAp hD hY hYN,
    centralizer_le_of_map hC⟩

end CFSG.AGLEmbeddingD2
