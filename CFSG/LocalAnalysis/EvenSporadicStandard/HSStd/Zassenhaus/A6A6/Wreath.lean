module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.WreathSw
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.A6InA8

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M22Std

variable {V : Type} [Group V] {G : Type} [Group G] {ρ : G →* MulAut V}

theorem Config.exists_wreath_of (hc : ∀ x y : V, x * y = y * x) (hs : ∀ x : V, x * x = 1)
    (hV : Nat.card V = 256) [Finite G] (hρ : Function.Injective ρ)
    (c : Config ρ) (hN : fusionOddCore G = ⊥)
    (hσ : ∀ (W : Type) [Group W] [Finite W], (∀ x y : W, x * y = y * x) → (∀ x : W, x * x = 1) →
      Nat.card W = 16 → ∀ A : Subgroup (MulAut W), Nonempty (A ≃* alternatingGroup (Fin 6)) →
      ∃ σ : ↥(normalizer (A : Set (MulAut W))) →* Equiv.Perm (Fin 6), Function.Injective σ) :
    ∃ f : G →* Equiv.Perm (Fin 2 × Fin 6), Function.Injective f ∧ ∀ g, f g ∈ wreathS6Z2 := by
  have hσ' : NormalizerHom := hσ
  by_cases h : ∃ g : G, cj g c.C = c.D
  · obtain ⟨g₁, hg₁⟩ := h
    exact c.exists_wreath_swap hσ' hc hs hV hρ ⟨c.conj_dichotomy hN, g₁, hg₁⟩
  · refine c.exists_wreath_ns hσ' hc hs hV hρ fun g => ?_
    rcases c.conj_dichotomy hN g with h1 | h1
    · exact h1
    · exact absurd ⟨g, h1.1⟩ h

theorem Config.exists_wreath (hc : ∀ x y : V, x * y = y * x) (hs : ∀ x : V, x * x = 1)
    (hV : Nat.card V = 256) [Finite G] (hρ : Function.Injective ρ)
    (c : Config ρ) (hN : fusionOddCore G = ⊥) :
    ∃ f : G →* Equiv.Perm (Fin 2 × Fin 6), Function.Injective f ∧ ∀ g, f g ∈ wreathS6Z2 :=
  c.exists_wreath_of hc hs hV hρ hN fun _ _ _ hc hs hW A ⟨eA⟩ =>
    exists_normalizer_hom hc hs hW A eA

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
