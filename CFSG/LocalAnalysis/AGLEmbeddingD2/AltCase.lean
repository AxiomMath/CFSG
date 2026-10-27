module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSurvivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Data

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}

theorem D2Escape.A_eq_of_map_eq (h : D2Escape p P M A H R)
    (hRA : (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) : A = R := by
  refine Subgroup.eq_of_le_of_card_ge h.A_le ?_
  rw [← h.card_map_eq le_rfl, ← h.card_map_eq h.A_le, hRA]

@[expose] def D2AltNoConfig : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (P : Sylow p G) (M A H : Subgroup G),
      D2Escape p P M A H A → D2EscapeMax p P M A → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* alternatingGroup (Fin (2 * p))) → False

@[expose] def D2AltSixCase : Prop := D2IndexCaseAt (.alternating 6 (by norm_num)) fun p => p = 3

theorem d2IndexCase_alt_of (hNo : D2AltNoConfig) (hA6 : D2AltSixCase) (n : ℕ)
    (hn : 5 ≤ 2 * n) : D2IndexCase (.alternating (2 * n) hn) := by
  intro G _ _ hglob hD1 p P M A H R hesc hmax hβ Rbar K hRbar hK ⟨e⟩
  have hp : p.Prime := hesc.prime
  have : Fact p.Prime := ⟨hp⟩
  have hnp : 2 * n = 2 * p := hK.eq_two_mul_of_alternating hn e
  have hnp' : n = p := by omega
  subst hnp'
  rcases (show n = 3 ∨ 5 ≤ n by
      have := hp.two_le
      have := hesc.ne_two
      rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hp) (by norm_num)
      · exact Or.inr h) with h3 | h5
  · subst h3
    exact hA6 G hglob hD1 3 rfl P M A H R hesc hmax hβ Rbar K hRbar hK ⟨e⟩
  · have hRA := hK.sylow_eq_of_alternating h5 e
    rw [hRbar] at hRA
    have hAR : A = R := hesc.A_eq_of_map_eq hRA
    subst hAR
    exact hNo G hglob hD1 n h5 P M A H hesc hmax hβ Rbar K hRbar hK ⟨e⟩

end CFSG.AGLEmbeddingD2
