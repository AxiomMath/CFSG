module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111SizeMax
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.AGL81TheoremC.CoprimeGamma

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2 CFSG.QuasiDihedralFusion

variable {G : Type} [Group G] [Finite G]

theorem core_le_of_base {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hμ : AGLMuAt p P M)
    {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N) :
    (primeComplementCore (G := N) p).map N.subtype ≤ M := by
  obtain ⟨H₁, R₁, he⟩ := hμ.escape
  haveI : Fact p.Prime := ⟨he.prime⟩
  obtain ⟨k, E, hk, hEB, hE, hEc, hΓ⟩ := exists_isStdE_of_isAGLQ he hB
  rw [map_primeComplementCore_eq]
  have hcard : p ^ (k - 1 + 1) ≤ Nat.card E := by
    rcases hk with rfl | rfl <;> simp [hEc]
  exact CFSG.LocalAnalysis.AGL81TheoremC.relPPrimeCore_le_of_glbCore_le hE hcard (hEB.trans hBN) hΓ

variable (G) in
@[expose] def AGL81NineThreeAt : Prop :=
  AGLGlobal G → ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), AGLMuAt p P M →
    ∀ B N : Subgroup G, IsAGLQ p M B → B ≤ N → GLBIsMaxTwoLocal N → ¬ N ≤ M →
      d1KBar p M N ≠ ⊥ →
      Hyp111NineThree p M N (d1KBar p M N) ∧
        Open.pRank p (d1PlusCore p N (d1KBar p M N)) ≤ 1 ∧
        NineThreeListGroup p (d1KBar p M N)

variable (G) in
@[expose] def AGL81NineSeventeenQ : Prop :=
  AGLGlobal G → ∀ (p : ℕ) (P : Sylow p G) (M H : Subgroup G), AGLMuAt p P M →
    GLBIsMaxTwoLocal H → ¬ H ≤ M →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) →
    ∀ B N : Subgroup G, IsAGLQ p M B → B ≤ H → GLBIsMaxTwoLocal N → ¬ N ≤ M → B ≤ N →
      AGLCovers p H N (d1KBar p M H) →
      d1KBar p M N ≠ ⊥ ∧ Hyp917At p M H N (d1KBar p M H) ∧ d1Kappa p M H ≤ d1Kappa p M N ∧
        ((∃ W : Subgroup G, ∃ _ : W ≤ H ⊓ N,
          (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
            d1KBar p M H ∧
          (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≤
            d1KBar p M N) ∨
        (∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y) ∨
        Involves (d1KBar p M N) (d1KBar p M H))

theorem agl81NineCompetitorQ_of (h93 : AGL81NineThreeAt G) (h917 : AGL81NineSeventeenQ G) :
    AGL81NineCompetitorQ G := by
  intro hg p P M H hμ hH hHM hK B N hB hBH hN hNM hBN hcov
  obtain ⟨hKN, h917N, hκ, hdisj⟩ := h917 hg p P M H hμ hH hHM hK B N hB hBH hN hNM hBN hcov
  obtain ⟨h93N, -, hlistN⟩ := h93 hg p P M hμ B N hB hBN hN hNM hKN
  exact ⟨⟨core_le_of_base hμ hB hBN, h93N, fun _ => hlistN, h917N, hκ⟩, hdisj⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
