module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAllData
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicSix

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput)

theorem exists_odd_evenLieOrder_POmega_eq {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f : ℕ} (hm : 1 ≤ m) (hf : 1 ≤ f) :
    ∃ r, Odd r ∧ F4Pilot.evenLieOrder t m f = 2 ^ (f * (m * (m - 1))) * r := by
  rcases ht with rfl | rfl
  · exact (Timmesfeld.Orders.profile_ordD hm hf).two
  · exact (Timmesfeld.Orders.profile_ordTwistedD hm hf).two

theorem evenLieOrder_POmega_five_one {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) :
    F4Pilot.evenLieOrder t 5 1 = 23499295948800 ∨
      F4Pilot.evenLieOrder t 5 1 = 25015379558400 := by
  rcases ht with rfl | rfl
  · left; decide
  · right; decide

theorem false_of_monster_POmega (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M) {σ : MulAut S}
    (hσ : orderOf σ = 2) {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f : ℕ}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) t m 2 f) : False := by
  obtain ⟨h41, h42⟩ := monster_two_part_card_quotient_center hMinn hMcomp hS hna e hσ hD
  have hm := four_le_of_lieModel_POmega ht hDm
  obtain ⟨r, hr, hO⟩ := exists_odd_evenLieOrder_POmega_eq (m := m) (f := f) ht (by omega)
    (one_le_of_lieModel_POmega ht hDm)
  have h := eq_forty_one_of_two_part hr ((card_of_lieModel_POmega_two ht hDm).trans hO) h41 h42
  have hev : Even (f * (m * (m - 1))) := (Nat.even_mul_pred_self m).mul_left f
  rw [h] at hev
  exact absurd hev (by decide)

@[expose] def omegaSporadicResidual (m f : ℕ) (s : TauCeti.SporadicName) : Prop :=
  (m = 4 ∧ f = 1) ∨ (m = 5 ∧ f = 1 ∧ (s = .Fi24Prime ∨ s = .B)) ∨ (m = 6 ∧ f = 1 ∧ s = .B)

instance (m f : ℕ) (s : TauCeti.SporadicName) : Decidable (omegaSporadicResidual m f s) := by
  unfold omegaSporadicResidual
  infer_instance

theorem omegaSporadicResidual_of_check {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f N : ℕ} {s : TauCeti.SporadicName}
    (hm : 4 ≤ m) (hf : 1 ≤ f) (hdvd : F4Pilot.evenLieOrder t m f ∣ N) (h47 : ¬ 2 ^ 47 ∣ N)
    (hcheck : ∀ m ∈ Finset.range 8, ∀ f ∈ Finset.range 4, 4 ≤ m → 1 ≤ f →
      f * (m * (m - 1)) ≤ 46 → omegaSporadicResidual m f s ∨
        (¬ F4Pilot.evenLieOrder .POmegaPlus m f ∣ N ∧
          ¬ F4Pilot.evenLieOrder .POmegaMinus m f ∣ N)) :
    omegaSporadicResidual m f s := by
  have h2 : f * (m * (m - 1)) ≤ 46 := by
    by_contra h
    exact h47 ((Nat.pow_dvd_pow 2 (by omega)).trans
      ((evenLieOrder_POmega_bounds ht hm hf).1.trans hdvd))
  have hm8 : m < 8 := by
    by_contra h
    have h56 : 8 * 7 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    have : m * (m - 1) ≤ f * (m * (m - 1)) := Nat.le_mul_of_pos_left _ hf
    omega
  have hf4 : f < 4 := by
    have h12 : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
    have : f * (4 * 3) ≤ f * (m * (m - 1)) := Nat.mul_le_mul_left f h12
    omega
  rcases hcheck m (Finset.mem_range.mpr hm8) f (Finset.mem_range.mpr hf4) hm hf h2 with
    h | ⟨hp, hn⟩
  · exact h
  · rcases ht with rfl | rfl
    · exact absurd hdvd hp
    · exact absurd hdvd hn

section Orders


theorem omegaSporadicResidual_of_dvd {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f) {s : TauCeti.SporadicName} (hs : s ≠ .M)
    (hdvd : F4Pilot.evenLieOrder t m f ∣ Nat.card (NativeSporadic.Carrier s)) :
    omegaSporadicResidual m f s := by
  have gen : ∀ N : ℕ, Nat.card (NativeSporadic.Carrier s) = N → ¬ 2 ^ 47 ∣ N →
      (∀ m ∈ Finset.range 8, ∀ f ∈ Finset.range 4, 4 ≤ m → 1 ≤ f →
        f * (m * (m - 1)) ≤ 46 → omegaSporadicResidual m f s ∨
          (¬ F4Pilot.evenLieOrder .POmegaPlus m f ∣ N ∧
            ¬ F4Pilot.evenLieOrder .POmegaMinus m f ∣ N)) →
      omegaSporadicResidual m f s :=
    fun N hN h47 hcheck => omegaSporadicResidual_of_check ht hm hf (hN ▸ hdvd) h47 hcheck
  cases s
  case M11 => exact gen _ Sporadic.Mathieu.card_M11 (by decide) (by decide)
  case M12 => exact gen _ Sporadic.Mathieu.card_M12 (by decide) (by decide)
  case M22 => exact gen _ Sporadic.Mathieu.card_M22 (by decide) (by decide)
  case M23 => exact gen _ EvenSmallLie.CatalogOrders.card_M23 (by decide) (by decide)
  case M24 => exact gen _ Sporadic.Mathieu.card_M24 (by decide) (by decide)
  case J1 => exact gen _ Sporadic.J1.card_J1 (by decide) (by decide)
  case J2 => exact gen _ Sporadic.J2.card_J2 (by decide) (by decide)
  case J3 => exact gen _ Sporadic.J3.card_J3 (by decide) (by decide)
  case J4 => exact gen _ Sporadic.J4.card_J4 (by decide) (by decide)
  case HS => exact gen _ Sporadic.HS.card_HS (by decide) (by decide)
  case McL => exact gen _ Sporadic.McL.card_McL (by decide) (by decide)
  case He => exact gen _ Sporadic.He.fam_he_order.1 (by decide) (by decide)
  case Ru => exact gen _ Sporadic.Ru.card_Ru (by decide) (by decide)
  case Suz => exact gen _ Sporadic.Suz.card_Suz (by decide) (by decide)
  case ONan => exact gen _ Sporadic.ON.card_ON (by decide) (by decide)
  case Co1 => exact gen _ Sporadic.Co1.card_Co1 (by decide) (by decide)
  case Co2 => exact gen _ Sporadic.Co2.card_Co2 (by decide) (by decide)
  case Co3 => exact gen _ Sporadic.Co3.card_Co3 (by decide) (by decide)
  case Fi22 => exact gen _ Sporadic.Fi22.card_Fi22 (by decide) (by decide)
  case Fi23 => exact gen _ Sporadic.Fi23.card_Fi23 (by decide) (by decide)
  case Fi24Prime => exact gen _ Sporadic.Fi24.card_Fi24prime (by decide) (by decide)
  case HN => exact gen _ Sporadic.HN.card_HN (by decide) (by decide)
  case Ly => exact gen _ Sporadic.Ly.card_Ly (by decide) (by decide)
  case Th => exact gen _ Monster.Existence.Compat.card_nativeTh (by decide) (by decide)
  case B => exact gen _ Monster.Existence.card_nativeB (by decide) (by decide)
  case M => exact absurd rfl hs

theorem false_of_sporadic_POmega (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f : ℕ}
    (hmf : ¬ (m = 4 ∧ f = 1)) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) t m 2 f) : False := by
  obtain ⟨s, ⟨e⟩⟩ := hsp
  by_cases hsM : s = .M
  · subst hsM
    exact false_of_monster_POmega hMinn hMcomp hS hna e hσ ht hD hDm
  have hc := card_of_lieModel_POmega_two ht hDm
  have hdvd : F4Pilot.evenLieOrder t m f ∣ Nat.card (NativeSporadic.Carrier s) := by
    rw [← hc, ← Nat.card_congr e.toEquiv]
    exact card_quotient_center_dvd_card_of_fixed D
  rcases omegaSporadicResidual_of_dvd ht (four_le_of_lieModel_POmega ht hDm)
      (one_le_of_lieModel_POmega ht hDm) hsM hdvd with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl, hs⟩ | ⟨rfl, rfl, rfl⟩
  · exact hmf ⟨rfl, rfl⟩
  · rcases hs with rfl | rfl
    · rcases fi24_card_quotient_center hS hna e hσ hD with h | h | h <;>
        rcases evenLieOrder_POmega_five_one ht with h' | h' <;> rw [hc, h'] at h <;>
        norm_num at h
    · rcases baby_card_quotient_center hS hna e hσ hD with h | h <;>
        rcases evenLieOrder_POmega_five_one ht with h' | h' <;> rw [hc, h'] at h <;>
        norm_num at h
  · rcases baby_card_quotient_center hS hna e hσ hD with h | h <;>
      rcases evenLieOrder_POmega_six_one ht with h' | h' <;> rw [hc, h'] at h <;>
      norm_num at h

theorem catOmegaSporadicAt_of_monster (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (m : ℕ) : CatOmegaSporadicAt m := by
  intro S _ _ hS hna hsp σ hσ t f D ht hD hDm _
  by_contra hmf
  exact false_of_sporadic_POmega hMinn hMcomp hS hna hsp hσ ht hmf hD hDm

end Orders

end CFSG.SeitzReduction.OmegaPilot
