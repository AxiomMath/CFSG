module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyClassical
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyOrth

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic

@[expose] def StandardPairDichotomyFE (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (e : ℕ), (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
    StatedLieAdmissible t 0 p e → StandardPairDichotomy p t 0 e

@[expose] def StandardPairDichotomyG2D4 (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (e : ℕ), (t = .G2 ∨ t = .trialityD4) →
    StatedLieAdmissible t 0 p e → StandardPairDichotomy p t 0 e

theorem standardPairDichotomy_of_FE {p : ℕ} [Fact p.Prime] (h : StandardPairDichotomyFE p)
    {t : StatedLieTag} {n e : ℕ} (hfund : Generic.IsFundTag t) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) (hadm : StatedLieAdmissible t n p e) :
    StandardPairDichotomy p t n e := by
  cases t with
  | PSL => exact standardPairDichotomy_psl hadm
  | PSU => exact standardPairDichotomy_psu hadm
  | PSp => exact standardPairDichotomy_psp hadm
  | POmegaOdd => exact standardPairDichotomy_pOmegaOdd hadm
  | POmegaPlus => exact standardPairDichotomy_pOmegaPlus hadm
  | POmegaMinus => exact standardPairDichotomy_pOmegaMinus hadm
  | G2 => exact absurd rfl hG2
  | F4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact h .F4 e (Or.inl rfl) hadm
  | E6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact h .E6 e (Or.inr (Or.inl rfl)) hadm
  | E7 =>
    obtain rfl : n = 0 := hadm.2.2
    exact h .E7 e (Or.inr (Or.inr (Or.inl rfl))) hadm
  | E8 =>
    obtain rfl : n = 0 := hadm.2.2
    exact h .E8 e (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hadm
  | twistedE6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact h .twistedE6 e (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hadm
  | trialityD4 => exact absurd rfl hD4
  | twistedB2 => exact absurd hfund (by simp [Generic.IsFundTag])
  | twistedG2 => exact absurd hfund (by simp [Generic.IsFundTag])
  | twistedF4 => exact absurd hfund (by simp [Generic.IsFundTag])
  | Tits => exact absurd hfund (by simp [Generic.IsFundTag])

theorem standardPairDichotomyFacts_of_exceptional {p : ℕ} [Fact p.Prime]
    (hFE : StandardPairDichotomyFE p) (hG : StandardPairDichotomyG2D4 p) :
    StandardPairDichotomyFacts p := by
  intro t n e hfund hadm
  by_cases hG2 : t = .G2
  · subst hG2
    obtain rfl : n = 0 := hadm.2.2.1
    exact hG .G2 e (Or.inl rfl) hadm
  by_cases hD4 : t = .trialityD4
  · subst hD4
    obtain rfl : n = 0 := hadm.2.2
    exact hG .trialityD4 e (Or.inr rfl) hadm
  exact standardPairDichotomy_of_FE hFE hfund hG2 hD4 hadm

end CFSG.ClassicalInvolution.ModelFacts
