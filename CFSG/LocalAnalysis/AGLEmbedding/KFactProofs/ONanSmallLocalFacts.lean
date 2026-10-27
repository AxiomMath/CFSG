module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallLocal

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

structure LocalFacts (p : ℕ) (K : Type) [Group K] [Finite K] (T : Sylow p K) : Prop where
  center : Subgroup.center K = ⊥
  centralizer_le : ∀ g : K, (∀ t ∈ (T : Subgroup K), g * t = t * g) → g ∈ (T : Subgroup K)
  torus : ∃ T₀ : Subgroup K, T₀ ≤ Subgroup.normalizer ((T : Subgroup K) : Set K) ∧
    p.Coprime (Nat.card T₀) ∧ (T : Subgroup K) ⊓ Subgroup.centralizer (T₀ : Set K) = ⊥
  invariant : ∀ V : Subgroup K, V ≤ (T : Subgroup K) → V ≠ ⊥ →
    Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K) →
    V = (T : Subgroup K) ∨ (V = centerOf (T : Subgroup K) ∧ centerOf (T : Subgroup K) ≠ T)

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem LocalFacts.mem_of_conj_fix {T : Sylow p K} (D : LocalFacts p K T) {g : K}
    (hg : ∀ t ∈ (T : Subgroup K), MulAut.conj g t = t) : g ∈ (T : Subgroup K) := by
  refine D.centralizer_le g fun t ht => ?_
  have := hg t ht
  rw [MulAut.conj_apply] at this
  calc g * t = (g * t * g⁻¹) * g := by group
    _ = t * g := by rw [this]

theorem oneSmallFacts_of_localFacts (hp : p.Prime) {T : Sylow p K} (D : LocalFacts p K T)
    (hA : AutFixInner p K T) (hPin : AutPInner p K) : OneSmallFacts p K T := by
  refine ⟨?_, D.torus, ?_⟩
  · intro Y hY _ hYN α hα
    have hin : ∀ Y : Subgroup (MulAut K), IsPGroup p Y →
        Y ≤ (MulAut.conj : K →* MulAut K).range :=
      fun Y hY α hα => hPin α (by
        obtain ⟨k, hk⟩ := hY ⟨α, hα⟩
        exact ⟨k, congrArg Subtype.val hk⟩)
    obtain ⟨u, hu, hαu⟩ := pLe_of_pInner hp T D.center hin Y hY (fun b hb β hβ =>
      (Subgroup.mem_normalizer_iff.1 (hYN ⟨b, hb, rfl⟩) β).1 hβ) α hα
    exact ⟨u, hu, hαu.symm⟩
  · intro V hVT hV hVN
    rcases D.invariant V hVT hV hVN with h | h
    · left
      intro f hf
      obtain ⟨g, hg⟩ := hA f fun t ht => hf t (h ▸ ht)
      exact ⟨g, D.mem_of_conj_fix fun t ht => by rw [hg]; exact hf t (h ▸ ht), hg.symm⟩
    · exact Or.inr h

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
