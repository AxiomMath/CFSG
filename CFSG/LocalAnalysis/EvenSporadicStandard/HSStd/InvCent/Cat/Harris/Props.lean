module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Classify

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open CFSG CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def HarrisKleinFree (t : StatedLieTag) (n p f : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S t n p f →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ D : Subgroup ↥(fixedSubgroup σ), A6Hyp σ D →
      ¬ OuterKlein σ

@[expose] def HarrisOddSharp (t : StatedLieTag) (n f : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S t n 3 f →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ D : Subgroup ↥(fixedSubgroup σ), A6Hyp σ D →
      Nat.card ↥(fixedSubgroup σ) ≠ 1440 ∧
        (σ ∈ (MulAut.conj : S →* MulAut S).range → Nat.card ↥(fixedSubgroup σ) ≠ 2880)

@[expose] def HarrisOmegaLarge (t : StatedLieTag) (n f : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S t n 3 f →
    ∀ σ : MulAut S, orderOf σ = 2 → 2880 < Nat.card ↥(fixedSubgroup σ)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
