module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicFourProved
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatSporadicFour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotFourXChar
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaFinal
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Neighbour
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapDescent
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueMain

public section

namespace CFSG.SeitzReduction

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.ComponentClassification.CatLeafProof (monsterInnerInput monsterLocalComponentsInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def CatSp6SporadicResidualAtF (f : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ s : TauCeti.SporadicName, Nonempty (S ≃* Blueprint.NativeSporadic.Carrier s) →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ D : Subgroup (fixedSubgroup σ),
      IsComponent D → Blueprint.LieModel D .PSp 3 2 f →
      (σ ∈ (MulAut.conj : S →* MulAut S).range ∨ F4Pilot.FixedCentralizerTwoFree σ D) →
      F4Pilot.sp6SporadicResidual f s → False

theorem catSp6SporadicResidual_iff_forall_atF :
    F4Pilot.CatSp6SporadicResidual ↔ ∀ f : ℕ, CatSp6SporadicResidualAtF f :=
  ⟨fun h f S _ _ hS hna s hs σ hσ D hD hDm hcase hr => h S hS hna s hs σ hσ f D hD hDm hcase hr,
    fun h S _ _ hS hna s hs σ hσ f D hD hDm hcase hr => h f S hS hna s hs σ hσ D hD hDm hcase hr⟩

theorem catSp2mSporadicResidualAtF_three_of_sp6 {f : ℕ} (h : CatSp6SporadicResidualAtF f) :
    SymplecticPilot.CatSp2mSporadicResidualAtF 3 f :=
  fun S _ _ hS hna s hs σ hσ D hD hDm hcase hr =>
    h S hS hna s hs σ hσ D hD hDm (hcase.imp And.left id)
      (SymplecticPilot.sp2mSporadicResidual_three_iff.mp hr)

section Base

theorem e7TwoPerpLeviDescentInput_holds : E8Pilot.E7TwoPerpLeviDescentInput :=
  fun _ _ _ _ _ => E7Pilot.perpLeviFrobDescent_E7_of_finite

section Residual

theorem catSp6SporadicResidualAtF_of_ne_one {f : ℕ} (hf : f ≠ 1) :
    CatSp6SporadicResidualAtF f := by
  intro S _ _ hS hna s hs σ hσ D hD hDm _ hr
  rcases Nat.lt_or_ge f 2 with h2 | h2
  · rcases hr with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  · exact SymplecticPilot.catSp6SporadicResidual_of_two_le S hS hna s hs σ hσ f h2 D hD hDm hr

theorem catSp6SporadicResidual_of_atF_one (h : CatSp6SporadicResidualAtF 1) :
    F4Pilot.CatSp6SporadicResidual :=
  catSp6SporadicResidual_iff_forall_atF.2 fun f =>
    (eq_or_ne f 1).elim (fun hf => hf ▸ h) catSp6SporadicResidualAtF_of_ne_one

theorem forall_catSp2mSporadicResidual_of_atF_three_one
    (h : SymplecticPilot.CatSp2mSporadicResidualAtF 3 1) :
    ∀ m : ℕ, 3 ≤ m → SymplecticPilot.CatSp2mSporadicResidual m := by
  intro m hm
  rcases (by omega : m = 3 ∨ 4 ≤ m) with rfl | h4
  · refine SymplecticPilot.catSp2mSporadicResidual_iff_forall_atF.2 fun f => ?_
    rcases (by omega : f = 0 ∨ f = 1 ∨ 2 ≤ f) with rfl | rfl | hf
    · intro S _ _ hS hna s hs σ hσ D hD hDm _ hr
      rcases SymplecticPilot.sp2mSporadicResidual_three_iff.mp hr with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
        omega
    · exact h
    · exact SymplecticPilot.catSp2mSporadicResidualAtF_of_two_le le_rfl hf
  · exact SymplecticPilot.catSp2mSporadicResidual_of_four_le h4

section Linear

theorem catSLmSporadic_of_three (h3 : LinearPilot.CatSLmSporadicAt 3) :
    LinearPilot.CatSLmSporadic := fun m hm =>
  (eq_or_ne m 3).elim (fun h => h ▸ h3) fun h =>
    LinearPilot.catSLmSporadicAt_of_four_le (by omega)

end Linear

end Residual

section Large

theorem e8TwoInput_of_gls3_fieldRow (hGLS : GLS3OddLieAutComponentsInput)
    (hF : E8Pilot.E8TwoFieldRowInput) : E8Pilot.E8TwoInput :=
  E8Pilot.e8TwoInput_of_fieldRow_of_descent
    (e7CatalogueClauses_of_xchar_monster hGLS monsterInnerInput monsterLocalComponentsInput)
    e7TwoPerpLeviDescentInput_holds hF

theorem seitzExclusion_highE8_of_final3 (hGLS : GLS3OddLieAutComponentsInput)
    (hF : E8Pilot.E8TwoFieldRowInput) : SeitzExclusion (HighExceptional .E8) :=
  seitzExclusion_highE8_of_final hGLS (e8TwoInput_of_gls3_fieldRow hGLS hF)

section E7

section F4

theorem seitzExclusion_highF4_of_final3 (hGLS : GLS3OddLieAutComponentsInput)
    (hres : CatSp6SporadicResidualAtF 1) (hECT : F4Pilot.E6RowCTQuotInput)
    (hEL : F4Pilot.E6RowXiCaseLInput) (hTCT : F4Pilot.TwistedE6RowCTQuotInput)
    (hTL : F4Pilot.TwistedE6RowXiCaseLInput) (h2 : F4Pilot.TwoRowsInput) :
    SeitzExclusion (HighExceptional .F4) :=
  seitzExclusion_highF4_of_xchar_caseL hGLS monsterInnerInput monsterLocalComponentsInput
    (catSp6SporadicResidual_of_atF_one hres) F4Pilot.graphPieceTablesInput_holds hECT hEL hTCT hTL
    h2

section Big

theorem spFourOrthInput_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    SymplecticPilot.SpFourOrthInput :=
  SymplecticPilot.spFourOrthInput_of_xchar hGLS (LinearPilot.catSLmSporadicAt_of_four_le le_rfl)

theorem seitzExclusion_highPSL_of_final3 (hGLS : GLS3OddLieAutComponentsInput)
    (h3 : LinearPilot.CatSLmSporadicAt 3) (hTwo : LinearPilot.LinearTwoInput) :
    SeitzExclusion HighPSL :=
  seitzExclusion_highPSL_of_xchar hGLS (catSLmSporadic_of_three h3) hTwo

theorem seitzExclusion_highPSp_of_final3 (hGLS : GLS3OddLieAutComponentsInput)
    (hres : SymplecticPilot.CatSp2mSporadicResidualAtF 3 1)
    (hGraph : SymplecticPilot.SpGraphRowsInput) (hThree : SymplecticPilot.SpThreeInput)
    (hTwo : SymplecticPilot.SpTwoInput) : SeitzExclusion HighPSp :=
  SymplecticPilot.seitzExclusion_highPSp_of_inputs_unique hGLS
    (fun m _ => CrossChar.sp2mNotOddLieInput m) monsterInnerInput monsterLocalComponentsInput
    (forall_catSp2mSporadicResidual_of_atF_three_one hres) (spFourOrthInput_of_gls3 hGLS) hGraph
    hThree hTwo

end Big

end F4

end E7

end Large

end Base

end CFSG.SeitzReduction
