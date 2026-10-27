module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatOdd

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def OmegaNotOddLieInputAt (m : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (t : StatedLieTag) (f : ℕ), (t = .POmegaPlus ∨ t = .POmegaMinus) →
    LieModel X t m 2 f → ¬ OddLieType X

theorem catOmegaOddLieAt_of_inputs (hGLS : GLS3OddLieAutComponentsInput) {m : ℕ}
    (hX : OmegaNotOddLieInputAt m) : CatOmegaOddLieAt m := by
  intro S _ _ _ _ hodd σ hσ t f D ht hD hDm
  obtain ⟨τ, n, p, e, hp, hp2, hadm, hmS⟩ := hodd
  rcases hGLS S τ n p e hp hp2 hadm hmS σ hσ D hD with ⟨τ', n', f', hadm', hm'⟩ | ⟨-, -, -, hL⟩
  · exact hX (D ⧸ center D) t f ht hDm ⟨τ', n', p, f', hp, hp2, hadm', hm'⟩
  · have h504 := F4Pilot.card_of_lieModel_PSL_two_two_three hL
    have hdvd' : Nat.card (D ⧸ center D) ∣ 504 := h504 ▸ card_quotient_dvd_card _
    exact absurd ((two_pow_twelve_dvd_card_of_lieModel_POmega ht hDm).trans hdvd') (by decide)

end CFSG.SeitzReduction.OmegaPilot
