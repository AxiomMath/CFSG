module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Props
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open CFSG CFSG.Open CFSG.Blueprint

theorem outerKlein_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {σ : MulAut S}
    (h : OuterKlein σ) : OuterKlein (MulAut.congr e σ) := by
  obtain ⟨α, β, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have key : ∀ γ : MulAut S, MulAut.congr e γ ∈ (MulAut.conj : S' →* MulAut S').range ↔
      γ ∈ (MulAut.conj : S →* MulAut S).range :=
    CFSG.ComponentClassification.CatFC.congr_mem_range_iff e
  refine ⟨MulAut.congr e α, MulAut.congr e β, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, h1]
  · rw [← map_mul, ← map_mul, h2]
  · rw [← map_mul, key]
    exact h3
  · rw [← map_mul, key]
    exact h4
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, key]
    exact h5
  · exact fun h => h6 ((key α).1 h)
  · exact fun h => h7 ((key β).1 h)
  · rw [← map_mul, key]
    exact h8

theorem harrisKleinFree_of_concrete {t : StatedLieTag} {n p f : ℕ}
    (H : ∀ (S : Type) [Group S] [Finite S], LieModel S t n p f →
      ∃ (X : Type) (_ : Group X) (_ : S ≃* X), ∀ σ : MulAut X, ¬ OuterKlein σ) :
    HarrisKleinFree t n p f := by
  intro S _ _ hm σ _ _ _ hk
  obtain ⟨X, _, e, hX⟩ := H S hm
  exact hX (MulAut.congr e σ) (outerKlein_congr e hk)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
