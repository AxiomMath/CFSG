module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2SwapMain
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutInput

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.SeitzReduction.OmegaPilot (OmegaCatalogueClausesAt)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)


@[expose] def E7TwoFieldRowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K]
    (e : L ≃* adjointGroup .E7 K) (t : G), E7Work L K t 1 → HR8FieldE7Two e t 1 → False

theorem hr8FieldE7Two_or_hr8SwapE7Two (hcat : OmegaCatalogueClausesAt 6) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {K : Type} [Field K] {t : G} (hw : E7Work L K t 1)
    (e : L ≃* adjointGroup .E7 K) : HR8FieldE7Two e t 1 ∨ HR8SwapE7Two e t := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  obtain ⟨A, hAJ, hA⟩ := exists_nonsplit_le_posJE7_two hK2
  have hA' : Nat.card A = Nat.card K + 1 := by rw [hA, hK2]
  have htX : t ∈ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) :=
    centralizer_le (map_subtype_le _) hw.mem_centralizer
  rcases field_or_swap_of_neighbourOvergroupOmega
      (hw.neighbour_overgroup_nonsplit_two hcat e hAJ hA rfl htX rfl) with h | h
  · exact .inl ⟨A, hAJ, hA', htX, h⟩
  · exact .inr ⟨A, hAJ, hA', htX, h⟩

theorem e7TwoInput_of_fieldRow (hcat : OmegaCatalogueClausesAt 6)
    (hO : ∀ (K : Type) [Field K], E7TwoOverlapInput K)
    (hF : E7TwoFieldRowInput) : E7TwoInput := by
  intro G _ _ L K _ e t hw
  rcases hr8FieldE7Two_or_hr8SwapE7Two hcat hw e with h | h
  · exact hF G L K e t hw h
  · exact false_of_swapRow_E7_two (hO K) hw e h

section Inputs


theorem e7TwoInput_of_fieldRow_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaPilot.OmegaNotOddLieInputAt 6) (hSpor : OmegaPilot.CatOmegaSporadicAt 6)
    (hO : ∀ (K : Type) [Field K], E7TwoOverlapInput K)
    (hF : E7TwoFieldRowInput) : E7TwoInput :=
  e7TwoInput_of_fieldRow (OmegaPilot.omegaCatalogueClausesAt_of_inputs hGLS hXodd hSpor) hO hF

theorem seitzExclusion_highE7_of_q2_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaPilot.OmegaNotOddLieInputAt 6) (hSpor : OmegaPilot.CatOmegaSporadicAt 6)
    (hO : ∀ (K : Type) [Field K], E7TwoOverlapInput K)
    (hF : E7TwoFieldRowInput) : SeitzExclusion (HighExceptional .E7) :=
  seitzExclusion_highE7_of_four_inputs hGLS hXodd hSpor
    (e7TwoInput_of_fieldRow_of_inputs hGLS hXodd hSpor hO hF)

end Inputs

end CFSG.SeitzReduction.E7Pilot
