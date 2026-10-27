module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatEvenOuterClassical

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def CatSp2mOddLie (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    OddLieType S → ∀ σ : MulAut S, orderOf σ = 2 → ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      IsComponent D → LieModel D .PSp m 2 f → False

@[expose] def Sp2mNotOddLieInput (m : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), LieModel X .PSp m 2 f → ¬ OddLieType X

theorem sp2mNotOddLieInput_three_iff : Sp2mNotOddLieInput 3 ↔ F4Pilot.Sp6NotOddLieInput :=
  Iff.rfl

theorem catSp6OddLie_iff : CatSp2mOddLie 3 ↔ F4Pilot.CatSp6OddLie :=
  Iff.rfl

theorem catSp2mOddLie_of_inputs (hGLS : GLS3OddLieAutComponentsInput) {m : ℕ}
    (hX : Sp2mNotOddLieInput m) : CatSp2mOddLie m := by
  intro S _ _ _ _ hodd σ hσ f D hD hDm
  obtain ⟨t, n, p, e, hp, hp2, hadm, hmS⟩ := hodd
  have hZD : center D = ⊥ :=
    F4Pilot.center_eq_bot_of_isQuasisimple hD.1 (F4Pilot.isSimpleGroup_of_lieModel_PSp hDm)
  rcases hGLS S t n p e hp hp2 hadm hmS σ hσ D hD with ⟨τ', n', f', hadm', hm'⟩ | ⟨-, -, -, hL⟩
  · exact hX D f hDm ⟨τ', n', p, f', hp, hp2, hadm',
      LieType.CurtisTits.lieModel_of_mulEquiv (F4Pilot.mulEquivCenterQuotient hZD) hm'⟩
  · have h8 := two_pow_eight_dvd_card_of_lieModel_PSp hDm
    rw [F4Pilot.card_of_lieModel_PSL_two_two_three hL] at h8
    exact absurd h8 (by decide)

end CFSG.SeitzReduction.SymplecticPilot
