module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Props
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open CFSG CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem harrisOddSharp_of_concrete {t : StatedLieTag} {n f : ℕ}
    (H : ∀ (S : Type) [Group S] [Finite S], LieModel S t n 3 f →
      ∃ (X : Type) (_ : Group X) (_ : Finite X) (_ : S ≃* X),
        ∀ σ : MulAut X, orderOf σ = 2 → ∀ D : Subgroup ↥(fixedSubgroup σ), A6Hyp σ D →
          Nat.card ↥(fixedSubgroup σ) ≠ 1440 ∧
            (σ ∈ (MulAut.conj : X →* MulAut X).range → Nat.card ↥(fixedSubgroup σ) ≠ 2880)) :
    HarrisOddSharp t n f := by
  intro S _ _ hm σ hσ D hD
  obtain ⟨X, _, _, e, hX⟩ := H S hm
  have hcard : Nat.card ↥(fixedSubgroup (MulAut.congr e σ)) = Nat.card ↥(fixedSubgroup σ) :=
    (Nat.card_congr (fixedEquiv e σ).toEquiv).symm
  obtain ⟨h1, h2⟩ := hX (MulAut.congr e σ) ((orderOf_congr e σ).trans hσ) _
    (a6Hyp_congr e σ D hD)
  exact ⟨by rwa [hcard] at h1, fun hin => by
    rw [← hcard]
    exact h2 ((congr_mem_range_iff e σ).2 hin)⟩

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
