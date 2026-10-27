module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatCovers

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut FixedCentralizerTwoFree centerFixedProjection
  orderOf_centerQuotientAut centerQuotientAut_mem_range odd_card_center_of_twoFree
  twoFree_centerQuotientAut)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall odd_card_center_of_twoSmall_inner
  twoSmall_centerQuotientAut)

@[expose] def CatSp2mCovers : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → ∀ τ : MulAut K, orderOf τ = 2 →
    ∀ (m f : ℕ) (D : Subgroup (fixedSubgroup τ)), IsComponent D → LieModel D .PSp m 2 f →
      orderOf (centerQuotientAut τ) = 2 ∧
        (τ ∈ (MulAut.conj : K →* MulAut K).range →
          centerQuotientAut τ ∈ (MulAut.conj : (K ⧸ center K) →* MulAut (K ⧸ center K)).range) ∧
        ∃ D' : Subgroup (fixedSubgroup (centerQuotientAut τ)), IsComponent D' ∧
          LieModel D' .PSp m 2 f ∧
          (FixedCentralizerTwoFree τ D →
            Odd (Nat.card (center K)) ∧ FixedCentralizerTwoFree (centerQuotientAut τ) D') ∧
          (τ ∈ (MulAut.conj : K →* MulAut K).range → FixedCentralizerTwoSmall τ D →
            Odd (Nat.card (center K)) ∧ FixedCentralizerTwoSmall (centerQuotientAut τ) D')

theorem catSp2mCovers : CatSp2mCovers := by
  intro K _ _ hK τ hτ m f D hD hDm
  have : Group.IsPerfect K := hK.1
  have hZD : center D = ⊥ :=
    F4Pilot.center_eq_bot_of_isQuasisimple hD.1 (F4Pilot.isSimpleGroup_of_lieModel_PSp hDm)
  obtain ⟨hD', ⟨e⟩⟩ := F4Pilot.isComponent_map_fixedProjection hD hZD
  refine ⟨orderOf_centerQuotientAut hτ, centerQuotientAut_mem_range,
    D.map (centerFixedProjection τ), hD', LieType.CurtisTits.lieModel_of_mulEquiv e hDm,
    fun hodd => ⟨odd_card_center_of_twoFree hτ hodd, twoFree_centerQuotientAut hD hτ hodd⟩,
    fun hin hsmall => ?_⟩
  have hZ := odd_card_center_of_twoSmall_inner hτ hin hsmall
  exact ⟨hZ, twoSmall_centerQuotientAut hD hZ hsmall⟩

theorem catSp6Covers_of_catSp2mCovers (h : CatSp2mCovers) : F4Pilot.CatSp6Covers := by
  intro K _ _ hK τ hτ f D hD hD6
  obtain ⟨h1, h2, D', hD', hD'6, h3, -⟩ := h K hK τ hτ 3 f D hD hD6
  exact ⟨h1, h2, D', hD', hD'6, h3⟩

end CFSG.SeitzReduction.SymplecticPilot
