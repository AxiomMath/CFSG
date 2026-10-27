module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveKSporMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def LFiveSevenRankFamilyInput (t : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ n f : ℕ, StatedLieAdmissible t n 7 f → LieModel S t n 7 f →
    ∀ τ : MulAut S, orderOf τ = 2 →
    ∀ D : Subgroup (fixedSubgroup τ), IsComponent D → LieModel (D ⧸ center D) .PSL 3 2 1 →
      (F4Pilot.FixedCentralizerTwoFree τ D ∨
        (τ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall τ D)) →
      ∀ E : Subgroup S, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 8

theorem lFiveSevenRankFamilyInput_of_not_admissible {t : StatedLieTag}
    (ht : ∀ n f : ℕ, ¬ StatedLieAdmissible t n 7 f) : LFiveSevenRankFamilyInput t :=
  fun _ _ _ _ _ n f hadm => absurd hadm (ht n f)

theorem lFiveSevenRankFamilyInput_of_twisted {t : StatedLieTag}
    (ht : t = .twistedB2 ∨ t = .twistedF4 ∨ t = .twistedG2 ∨ t = .Tits) :
    LFiveSevenRankFamilyInput t := by
  refine lFiveSevenRankFamilyInput_of_not_admissible fun n f hadm => ?_
  rcases ht with rfl | rfl | rfl | rfl <;> obtain ⟨-, -, -, h, -⟩ := hadm <;> omega

theorem eq_seven_of_pow_eq_seven {p g : ℕ} (hp : p.Prime) (h : p ^ g = 7) : p = 7 ∧ g = 1 := by
  have hg : g ≠ 0 := by
    rintro rfl
    simp at h
  have hdvd : p ∣ 7 := h ▸ dvd_pow_self p hg
  have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hdvd
  subst hp7
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 7) (h.trans (pow_one 7).symm)⟩

section Cert


theorem eq_seven_of_lieModel_PSL_three_two {X : Type} [Group X] (hX : LieModel X .PSL 3 2 1)
    {t : StatedLieTag} {n p g : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p g)
    (h : LieModel X t n p g) : t = .PSL ∧ n = 2 ∧ p ^ g = 7 := by
  have hadm2 := CrossChar.statedLieAdmissible_of_lieModel hX
  have hT : t ≠ .Tits := by
    rintro rfl
    exact hp2 hadm.2.2.2.1
  rcases CrossChar.crossChar_arith hadm2 hadm hp2
      (CrossChar.card_mul_lieOrderDivisor_of_ne_Tits hadm2 hX (by decide))
      (CrossChar.card_mul_lieOrderDivisor_of_ne_Tits hadm h hT) with
    ⟨-, h1, -⟩ | ⟨-, -, -, h1, h2, h7⟩ | ⟨h1, -⟩
  · exact absurd h1 (by decide)
  · exact ⟨h1, h2, h7⟩
  · exact absurd h1 (by decide)

theorem lFiveSmallOddLieRankInput_of_seven (hGLS : GLS3OddLieAutComponentsInput)
    (h7 : ∀ t, LFiveSevenRankFamilyInput t) : LFiveSmallOddLieRankInput := by
  intro S _ _ hS hna hodd τ hτ D hD hDm h2 E hE
  obtain ⟨t, n, p, f, hp, hp2, hadm, hL⟩ := hodd
  rcases hGLS S t n p f hp hp2 hadm hL τ hτ D hD with ⟨t', n', f', hadm', hL'⟩ | ⟨-, -, -, hK⟩
  · obtain ⟨-, -, hpow⟩ := eq_seven_of_lieModel_PSL_three_two hDm hp2 hadm' hL'
    obtain ⟨rfl, -⟩ := eq_seven_of_pow_eq_seven hp hpow
    exact h7 t S hS hna n f hadm hL τ hτ D hD hDm h2 E hE
  · exfalso
    have hDs := isSimpleGroup_of_lieModel_PSL hK
    have h504 : Nat.card D = 504 := by
      rw [card_of_lieModel_PSL_two hK]
      decide
    have h168 := card_of_lieModel_PSL_three_two hDm
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (center D)
    rw [h504, h168] at hmul
    rcases hDs.eq_bot_or_eq_top_of_normal (center D) with hb | ht
    · rw [hb, card_bot] at hmul
      norm_num at hmul
    · rw [ht, card_top, h504] at hmul
      norm_num at hmul

end Cert

section Final


theorem lFiveSmallKindRankInput_of_seven (hGLS : GLS3OddLieAutComponentsInput)
    (h7 : ∀ t, LFiveSevenRankFamilyInput t) : LFiveSmallKindRankInput :=
  lFiveSmallKindRankInput_of_oddLie (lFiveSmallOddLieRankInput_of_seven hGLS h7)

end Final

end CFSG.SeitzReduction.LinearPilot
