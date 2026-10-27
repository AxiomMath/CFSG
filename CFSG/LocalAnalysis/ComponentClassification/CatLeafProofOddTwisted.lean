module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def OddTwistedE6InnerInput : Prop :=
  ∀ (J : Type) [Group J] (p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible .twistedE6 0 p f →
    Blueprint.LieModel J .twistedE6 0 p f → ∀ α : MulAut J, orderOf α = 2 →
      α ∈ (MulAut.conj : J →* MulAut J).range →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → OddLieCentralQuotient p L

@[expose] def OddTwistedE6OuterInput : Prop :=
  ∀ (J : Type) [Group J] (p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible .twistedE6 0 p f →
    Blueprint.LieModel J .twistedE6 0 p f → ∀ α : MulAut J, orderOf α = 2 →
      α ∉ (MulAut.conj : J →* MulAut J).range →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → OddLieCentralQuotient p L

@[expose] def OddTrialityInnerInput : Prop :=
  ∀ (J : Type) [Group J] (p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible .trialityD4 0 p f →
    Blueprint.LieModel J .trialityD4 0 p f → ∀ α : MulAut J, orderOf α = 2 →
      α ∈ (MulAut.conj : J →* MulAut J).range →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → OddLieCentralQuotient p L

@[expose] def OddTrialityOuterInput : Prop :=
  ∀ (J : Type) [Group J] (p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible .trialityD4 0 p f →
    Blueprint.LieModel J .trialityD4 0 p f → ∀ α : MulAut J, orderOf α = 2 →
      α ∉ (MulAut.conj : J →* MulAut J).range →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → OddLieCentralQuotient p L

@[expose] def OddReeInnerInput : Prop :=
  ∀ (J : Type) [Group J] (f : ℕ), StatedLieAdmissible .twistedG2 0 3 f →
    Blueprint.LieModel J .twistedG2 0 3 f → ∀ α : MulAut J, orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → OddLieCentralQuotient 3 L

theorem gls3OddFamilyInput_twistedE6 (hin : OddTwistedE6InnerInput)
    (hout : OddTwistedE6OuterInput) : GLS3OddFamilyInput .twistedE6 := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  obtain rfl : n = 0 := hadm.2.2
  refine Or.inl ?_
  by_cases hi : α ∈ (MulAut.conj : J →* MulAut J).range
  · exact hin J p f hp hp2 hadm hm α hα hi Kc hKc
  · exact hout J p f hp hp2 hadm hm α hα hi Kc hKc

theorem gls3OddFamilyInput_trialityD4 (hin : OddTrialityInnerInput)
    (hout : OddTrialityOuterInput) : GLS3OddFamilyInput .trialityD4 := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  obtain rfl : n = 0 := hadm.2.2
  refine Or.inl ?_
  by_cases hi : α ∈ (MulAut.conj : J →* MulAut J).range
  · exact hin J p f hp hp2 hadm hm α hα hi Kc hKc
  · exact hout J p f hp hp2 hadm hm α hα hi Kc hKc

theorem gls3OddFamilyInput_twistedG2 (hin : OddReeInnerInput) :
    GLS3OddFamilyInput .twistedG2 := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  have hn0 : n = 0 := hadm.2.2.1
  have hp3 : p = 3 := hadm.2.2.2.1
  subst hn0
  subst hp3
  exact Or.inl (hin J f hadm hm α hα Kc hKc)

end CFSG.ComponentClassification.CatLeafProof
