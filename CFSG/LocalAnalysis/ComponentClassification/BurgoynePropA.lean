module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSU
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePOmegaOdd
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePOmegaPlus4

public section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit CFSG.Assembly.LowTwoRank

@[expose] def BurgoynePropAPlusFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsM4 X → ∀ p f : ℕ, p ≠ 2 →
    LieModel (GeneralizedFitting.subgroup X) .POmegaPlus 4 p f →
    ∀ t : X, orderOf t = 2 → ∀ Y : Subgroup X, Y ≠ ⊥ → Y ≤ oddCentralizerCore t →
      PropAConclusion X t Y

@[expose] def BurgoynePropAExceptional : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsM4 X →
    ∀ (τ : StatedLieTag) (n p f : ℕ), τ ∈ oddExceptionalTags → p ≠ 2 →
      LieModel (GeneralizedFitting.subgroup X) τ n p f →
    ∀ t : X, orderOf t = 2 → ∀ Y : Subgroup X, Y ≠ ⊥ → Y ≤ oddCentralizerCore t →
      PropAConclusion X t Y

theorem burgoynePropAExceptional_of_inputs (h1 : BurgoyneExcOddCoreInput)
    (h2 : BurgoynePropAE6E7) : BurgoynePropAExceptional := by
  intro X _ _ hX τ n p f hτ hp2 hL t ht Y hY hYO
  by_cases hτ' : τ ∈ torusExceptionalTags
  · exact h2 X hX τ n p f hτ' hp2 hL t ht Y hY hYO
  · have hbot := h1 X hX.1 hX.2.1 τ n p f hτ hτ' hp2 hL t ht
    rw [hbot] at hYO
    exact absurd (le_bot_iff.1 hYO) hY

theorem burgoynePropA_of_cases (h4 : BurgoynePropAPlusFour) (hexc : BurgoynePropAExceptional) :
    BurgoynePropA := by
  rw [burgoynePropA_iff]
  intro X _ _ hX t ht Y hY hYO
  obtain ⟨τ, n, p, f, -, hp2, hadm, hL⟩ := hX.2.2.1
  cases τ with
  | PSL => exact PSL.burgoynePropA_PSL X hX hp2 hL t ht Y hY hYO
  | PSU => exact U.burgoynePropA_PSU X hX hp2 hL t ht Y hY hYO
  | PSp => exact Sp.burgoynePropA_PSp X hX hp2 hL t ht Y hY hYO
  | POmegaOdd => exact O.burgoynePropA_POmegaOdd X hX hp2 hL t ht Y hY hYO
  | POmegaMinus => exact O.burgoynePropA_POmegaMinus X hX hp2 hL t ht Y hY hYO
  | POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · obtain rfl : n = 4 := by omega
      exact h4 X hX p f hp2 hL t ht Y hY hYO
    · exact O.burgoynePropA_POmegaPlus X hX hp2 h5 hL t ht Y hY hYO
  | G2 => exact hexc X hX _ n p f (by decide) hp2 hL t ht Y hY hYO
  | F4 => exact hexc X hX _ n p f (by decide) hp2 hL t ht Y hY hYO
  | E6 => exact hexc X hX _ n p f (by decide) hp2 hL t ht Y hY hYO
  | E7 => exact hexc X hX _ n p f (by decide) hp2 hL t ht Y hY hYO
  | E8 => exact hexc X hX _ n p f (by decide) hp2 hL t ht Y hY hYO
  | twistedE6 => exact hexc X hX _ n p f (by decide) hp2 hL t ht Y hY hYO
  | trialityD4 => exact hexc X hX _ n p f (by decide) hp2 hL t ht Y hY hYO
  | twistedG2 => exact hexc X hX _ n p f (by decide) hp2 hL t ht Y hY hYO
  | twistedB2 => exact absurd hadm.2.2.2.1 hp2
  | twistedF4 => exact absurd hadm.2.2.2.1 hp2
  | Tits => exact absurd hadm.2.2.2.1 hp2

theorem burgoynePropA_of_inputs (hT1 : BurgoyneD4TrialityConjInput)
    (hT2 : BurgoyneD4TrialityOddCoreInput) (hE1 : BurgoyneExcOddCoreInput)
    (hE2 : BurgoynePropAE6E7) : BurgoynePropA :=
  burgoynePropA_of_cases (fun X _ _ hX _ _ hp2 hL t ht Y hY hYO =>
    O.burgoynePropA_POmegaPlus4 hT1 hT2 X hX hp2 hL t ht Y hY hYO)
    (burgoynePropAExceptional_of_inputs hE1 hE2)

end CFSG.ComponentClassification.Burgoyne
