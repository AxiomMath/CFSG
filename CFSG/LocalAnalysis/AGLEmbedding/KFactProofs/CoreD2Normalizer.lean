module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Lines

public section

namespace CFSG.AGLEmbedding.CoreD2

open CFSG.Open

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

@[expose] def NormalizerGens (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∃ E : Subgroup G, Nat.card E = p ^ 3 ∧
    ∀ A : Subgroup G, A ≤ E → IsElemAbelian p A → Nat.card A = p ^ 2 →
      ∃ Γ : Set G, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ, ∃ Q, Q ≤ A ∧ Q ≠ ⊥ ∧
        g ∈ Subgroup.normalizer (Q : Set G)

theorem one_le_pRank_of_le (hp : p.Prime) {A Q : Subgroup G} (hA : IsElemAbelian p A)
    (hQA : Q ≤ A) (hQ : Q ≠ ⊥) : 1 ≤ CFSG.Open.pRank p Q := by
  obtain ⟨y, hyQ, hy1⟩ := (Subgroup.bot_or_exists_ne_one Q).resolve_left hQ
  have hyp : y ^ p = 1 := hA.2 y (hQA hyQ)
  have : Fact p.Prime := ⟨hp⟩
  exact CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.zpowers_le.2 hyQ)
    (isElemAbelian_zpowers hyp)
    (by rw [Nat.card_zpowers, orderOf_eq_prime hyp hy1, pow_one])

theorem coreGenerationVOf_of_normalizerGens (hp : p.Prime) (h : NormalizerGens G p) :
    CoreGenerationVOf G p := by
  obtain ⟨E, hEc, hE⟩ := h
  refine ⟨E, IsPGroup.of_card hEc, hEc, fun A hAE hAe hAc => ?_⟩
  obtain ⟨Γ, hΓ, hn⟩ := hE A hAE hAe hAc
  refine ⟨Γ, hΓ, fun g hg => Or.inr ?_⟩
  obtain ⟨Q, hQA, hQ, hgQ⟩ := hn g hg
  exact ⟨Q, hQA, one_le_pRank_of_le hp hAe hQA hQ, hgQ⟩

theorem glbCore_one_eq_top_of_normalizer_gens (hp : p.Prime) {A : Subgroup G}
    (hA : IsElemAbelian p A) {Γ : Set G} (hΓ : Subgroup.closure Γ = ⊤)
    (h : ∀ g ∈ Γ, ∃ Q, Q ≤ A ∧ Q ≠ ⊥ ∧ g ∈ Subgroup.normalizer (Q : Set G)) :
    GLBCore p 1 A = ⊤ := by
  rw [eq_top_iff, ← hΓ, Subgroup.closure_le]
  intro g hg
  obtain ⟨Q, hQA, hQ, hgQ⟩ := h g hg
  exact CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1 hQA (one_le_pRank_of_le hp hA hQA hQ) hgQ

end CFSG.AGLEmbedding.CoreD2
