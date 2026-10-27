module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def Sp6NotOddLieInput : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), LieModel X .PSp 3 2 f → ¬ OddLieType X

theorem card_of_lieModel_PSL_two_two_three {X : Type} [Group X]
    (h : LieModel X .PSL 2 2 3) : Nat.card X = 504 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight (h.statedClassicalModel (by decide))

noncomputable def mulEquivCenterQuotient {X : Type*} [Group X] (h : center X = ⊥) :
    X ⧸ center X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem catSp6OddLie_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : Sp6NotOddLieInput) : CatSp6OddLie := by
  intro S _ _ _ _ hodd σ hσ f D hD hD6
  obtain ⟨t, n, p, e, hp, hp2, hadm, hm⟩ := hodd
  have hZD : center D = ⊥ :=
    center_eq_bot_of_isQuasisimple hD.1 (isSimpleGroup_of_lieModel_PSp hD6)
  rcases hGLS S t n p e hp hp2 hadm hm σ hσ D hD with ⟨τ', n', f', hadm', hm'⟩ | ⟨-, -, -, hL⟩
  · exact hX D f hD6 ⟨τ', n', p, f', hp, hp2, hadm',
      LieType.CurtisTits.lieModel_of_mulEquiv (mulEquivCenterQuotient hZD) hm'⟩
  · have h1 := card_of_lieModel_PSL_two_two_three hL
    have h2 := two_pow_nine_le_card_of_lieModel_PSp_three_two hD6
    omega

end CFSG.SeitzReduction.F4Pilot
