module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatStatement
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenInner

public section

namespace CFSG.SeitzReduction.E8Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut FixedCentralizerTwoFree)

section Covers


theorem center_eq_bot_of_lieModel_E7 {X : Type} [Group X] (hq : IsQuasisimple X) {n p f : ℕ}
    (h : LieModel X .E7 n p f) : center X = ⊥ :=
  F4Pilot.center_eq_bot_of_isQuasisimple hq (isSimpleGroup_of_lieModel_E7 h)

theorem catE7Covers : CatE7Covers := by
  intro K _ _ hK τ hτ f D hD hD7
  have : Group.IsPerfect K := hK.1
  obtain ⟨hD', ⟨e⟩⟩ :=
    F4Pilot.isComponent_map_fixedProjection hD (center_eq_bot_of_lieModel_E7 hD.1 hD7)
  exact ⟨F4Pilot.orderOf_centerQuotientAut hτ, F4Pilot.centerQuotientAut_mem_range,
    D.map (F4Pilot.centerFixedProjection τ), hD', LieType.CurtisTits.lieModel_of_mulEquiv e hD7,
    fun hodd => ⟨F4Pilot.odd_card_center_of_twoFree hτ hodd,
      F4Pilot.twoFree_centerQuotientAut hD hτ hodd⟩⟩

end Covers

theorem catE7EvenInner :
    CatE7EvenInner := by
  intro S _ _ hS hna heven σ hσ hin f D hD _
  have := hS
  exact F4Pilot.false_of_isComponent_fixedSubgroup_inner hna
    (ComponentClassification.CatLeaf.involutionCentralizersComponentFree_of_evenLieType heven) hσ
    hin hD

end CFSG.SeitzReduction.E8Pilot
