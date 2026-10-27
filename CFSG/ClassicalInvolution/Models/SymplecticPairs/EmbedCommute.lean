module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {n m₁ m₂ : ℕ}

theorem commute_spEmbed_of_disjoint {σ : Fin m₁ → Fin n} {τ : Fin m₂ → Fin n}
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hdisj : Disjoint (Set.range σ) (Set.range τ))
    (x : StatedSp m₁ K) (y : StatedSp m₂ K) :
    Commute (spEmbed σ hσ x) (spEmbed τ hτ y) := by
  have hx : spEmbed σ hσ x ∈ suppGroup (Set.range (Sum.map σ σ)) := by
    rw [← range_spEmbed hσ]
    exact ⟨x, rfl⟩
  have hsub : Set.range (Sum.map τ τ) ⊆ (Set.range (Sum.map σ σ))ᶜ := by
    rintro z ⟨w, rfl⟩ hz
    rcases w with a | a
    · obtain ⟨v, hv⟩ := hz
      rcases v with b | b
      · exact hdisj.le_bot ⟨⟨b, Sum.inl_injective hv⟩, ⟨a, rfl⟩⟩
      · simp at hv
    · obtain ⟨v, hv⟩ := hz
      rcases v with b | b
      · simp at hv
      · exact hdisj.le_bot ⟨⟨b, Sum.inr_injective hv⟩, ⟨a, rfl⟩⟩
  have hy : spEmbed τ hτ y ∈ suppGroup ((Set.range (Sum.map σ σ))ᶜ) :=
    suppGroup_mono hsub (by rw [← range_spEmbed hτ]; exact ⟨y, rfl⟩)
  exact commute_suppGroup_compl hx hy

end CFSG.ClassicalInvolution.Models.SymplecticPairs

end
