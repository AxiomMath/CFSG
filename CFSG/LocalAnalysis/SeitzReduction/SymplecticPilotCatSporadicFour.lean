module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAllData
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatInputsSporadic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

@[expose] def CatSp2mSporadicResidualAtF (m f : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ s : TauCeti.SporadicName, Nonempty (S ≃* NativeSporadic.Carrier s) →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ D : Subgroup (fixedSubgroup σ),
      IsComponent D → LieModel D .PSp m 2 f →
      ((σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D) ∨
        FixedCentralizerTwoFree σ D) →
      sp2mSporadicResidual m f s → False

theorem catSp2mSporadicResidual_iff_forall_atF {m : ℕ} :
    CatSp2mSporadicResidual m ↔ ∀ f : ℕ, CatSp2mSporadicResidualAtF m f :=
  ⟨fun h f S _ _ hS hna s hs σ hσ D hD hDm hcase hr => h S hS hna s hs σ hσ f D hD hDm hcase hr,
    fun h S _ _ hS hna s hs σ hσ f D hD hDm hcase hr => h f S hS hna s hs σ hσ D hD hDm hcase hr⟩

theorem card_quotient_center_of_lieModel_PSp {X : Type} [Group X] {D : Subgroup X}
    (hD : IsComponent D) {m f : ℕ} (hDm : LieModel D .PSp m 2 f) :
    Nat.card (D ⧸ center D) = Open.ordBC m (2 ^ f) := by
  have hZ : center D = ⊥ :=
    F4Pilot.center_eq_bot_of_isQuasisimple hD.1 (F4Pilot.isSimpleGroup_of_lieModel_PSp hDm)
  rw [Nat.card_congr (F4Pilot.mulEquivCenterQuotient hZ).toEquiv]
  exact card_of_lieModel_PSp_two_pow hDm

theorem ordBC_four_one_eq : Open.ordBC 4 (2 ^ 1) = 47377612800 := by decide

theorem ordBC_five_six_one_eq {m : ℕ} (hm : m = 5 ∨ m = 6) :
    Open.ordBC m (2 ^ 1) = 24815256521932800 ∨
      Open.ordBC m (2 ^ 1) = 208114637736580743168000 := by
  rcases hm with rfl | rfl
  · left; decide
  · right; decide

theorem ordBC_three_two_eq : Open.ordBC 3 (2 ^ 2) = 4106059776000 := by decide

section Residual

theorem catSp2mSporadicResidual_of_four_le {m : ℕ} (hm : 4 ≤ m) : CatSp2mSporadicResidual m := by
  intro S _ _ hS hna s ⟨e⟩ σ hσ f D hD hDm _ hr
  have hc := card_quotient_center_of_lieModel_PSp hD hDm
  unfold sp2mSporadicResidual at hr
  rcases hr with ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨rfl, rfl, hs⟩ | ⟨hm56, rfl, rfl⟩
  · omega
  · omega
  · rw [ordBC_four_one_eq] at hc
    rcases hs with rfl | rfl | rfl
    · have h11 := OmegaPilot.fi23_eleven_dvd_card_quotient_center hS hna e hσ hD
      rw [hc] at h11
      norm_num at h11
    · rcases OmegaPilot.fi24_card_quotient_center hS hna e hσ hD with h | h | h <;>
        rw [hc] at h <;> norm_num at h
    · rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD with h | h <;>
        rw [hc] at h <;> norm_num at h
  · rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD with h | h <;>
      rcases ordBC_five_six_one_eq hm56 with h' | h' <;> rw [hc, h'] at h <;> norm_num at h

theorem false_of_baby_PSp_three_two {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .B) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 2) : False := by
  have hc := card_quotient_center_of_lieModel_PSp hD hDm
  rw [ordBC_three_two_eq] at hc
  rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD with h | h <;>
    rw [hc] at h <;> norm_num at h

theorem catSp2mSporadicResidual_three_of_two_le (S : Type) [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (s : TauCeti.SporadicName)
    (hs : Nonempty (S ≃* NativeSporadic.Carrier s)) (σ : MulAut S) (hσ : orderOf σ = 2) (f : ℕ)
    (hf : 2 ≤ f) (D : Subgroup (fixedSubgroup σ)) (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 f) (hr : sp2mSporadicResidual 3 f s) : False := by
  obtain ⟨e⟩ := hs
  rcases sp2mSporadicResidual_three_iff.mp hr with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
  · omega
  · exact false_of_baby_PSp_three_two hS hna e hσ hD hDm

theorem catSp6SporadicResidual_of_two_le (S : Type) [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (s : TauCeti.SporadicName)
    (hs : Nonempty (S ≃* NativeSporadic.Carrier s)) (σ : MulAut S) (hσ : orderOf σ = 2) (f : ℕ)
    (hf : 2 ≤ f) (D : Subgroup (fixedSubgroup σ)) (hD : IsComponent D)
    (hDm : LieModel D .PSp 3 2 f) (hr : F4Pilot.sp6SporadicResidual f s) : False :=
  catSp2mSporadicResidual_three_of_two_le S hS hna s hs σ hσ f hf D hD hDm
    (sp2mSporadicResidual_three_iff.mpr hr)

theorem catSp2mSporadicResidualAtF_of_two_le {m f : ℕ} (hm : 3 ≤ m) (hf : 2 ≤ f) :
    CatSp2mSporadicResidualAtF m f := by
  intro S _ _ hS hna s hs σ hσ D hD hDm _ hr
  rcases (by omega : m = 3 ∨ 4 ≤ m) with rfl | h4
  · exact catSp2mSporadicResidual_three_of_two_le S hS hna s hs σ hσ f hf D hD hDm hr
  · exact not_sp2mSporadicResidual (.inr ⟨h4, hf⟩) hr

end Residual

end CFSG.SeitzReduction.SymplecticPilot
