module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAllData
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicSix

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (ordA)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput)

theorem one_le_of_lieModel_PSL {X : Type} [Group X] {m f : ℕ} (h : LieModel X .PSL m 2 f) :
    1 ≤ f :=
  (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl h).1.2.1

theorem false_of_monster_PSL (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M) {σ : MulAut S}
    (hσ : orderOf σ = 2) {m f : ℕ} (hm : 3 ≤ m) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) .PSL m 2 f) : False := by
  obtain ⟨h41, h42⟩ :=
    OmegaPilot.monster_two_part_card_quotient_center hMinn hMcomp hS hna e hσ hD
  have hf := one_le_of_lieModel_PSL hDm
  obtain ⟨r, hr, hO⟩ := (Timmesfeld.Orders.profile_ordA (n := m - 1) (f := f) (by omega) hf).two
  have h := OmegaPilot.eq_forty_one_of_two_part hr ((card_of_lieModel_PSL_two hDm).trans hO)
    h41 h42
  rw [show m - 1 + 1 = m by omega] at h
  have hm10 : m < 10 := by
    by_contra h'
    have h90 : 9 * 10 ≤ (m - 1) * m := Nat.mul_le_mul (by omega) (by omega)
    have : (m - 1) * m / 2 ≤ f * ((m - 1) * m / 2) := Nat.le_mul_of_pos_left _ hf
    omega
  interval_cases m <;> omega

@[expose] def slmSporadicResidual (m f : ℕ) (s : TauCeti.SporadicName) : Prop :=
  (m = 4 ∧ f = 1) ∨ (m = 4 ∧ f = 2 ∧ (s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B)) ∨
    (m = 5 ∧ f = 1 ∧ (s = .J4 ∨ s = .Th ∨ s = .B)) ∨ (m = 6 ∧ f = 1 ∧ (s = .Th ∨ s = .B)) ∨
    ((m = 5 ∨ m = 6) ∧ f = 2 ∧ s = .B)

instance (m f : ℕ) (s : TauCeti.SporadicName) : Decidable (slmSporadicResidual m f s) := by
  unfold slmSporadicResidual
  infer_instance

theorem slmSporadicResidual_of_check {m f N : ℕ} {s : TauCeti.SporadicName} (hm : 4 ≤ m)
    (hf : 1 ≤ f) (hdvd : ordA (m - 1) (2 ^ f) ∣ N) (h47 : ¬ 2 ^ 47 ∣ N)
    (hcheck : ∀ m ∈ Finset.range 11, ∀ f ∈ Finset.range 8, 4 ≤ m → 1 ≤ f →
      f * ((m - 1) * m / 2) ≤ 46 → slmSporadicResidual m f s ∨ ¬ ordA (m - 1) (2 ^ f) ∣ N) :
    slmSporadicResidual m f s := by
  have hb := (ordA_two_pow_bounds (n := m - 1) (by omega) hf).1
  rw [show m - 1 + 1 = m by omega] at hb
  have h2 : f * ((m - 1) * m / 2) ≤ 46 := by
    by_contra h
    exact h47 ((Nat.pow_dvd_pow 2 (by omega)).trans (hb.trans hdvd))
  have hm11 : m < 11 := by
    by_contra h
    have h110 : 10 * 11 ≤ (m - 1) * m := Nat.mul_le_mul (by omega) (by omega)
    have : (m - 1) * m / 2 ≤ f * ((m - 1) * m / 2) := Nat.le_mul_of_pos_left _ hf
    omega
  have hf8 : f < 8 := by
    have h12 : 3 * 4 ≤ (m - 1) * m := Nat.mul_le_mul (by omega) hm
    have : f * 6 ≤ f * ((m - 1) * m / 2) := Nat.mul_le_mul_left f (by omega)
    omega
  rcases hcheck m (Finset.mem_range.mpr hm11) f (Finset.mem_range.mpr hf8) hm hf h2 with h | h
  · exact h
  · exact absurd hdvd h

section Orders


theorem slmSporadicResidual_of_dvd {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f)
    {s : TauCeti.SporadicName} (hs : s ≠ .M)
    (hdvd : ordA (m - 1) (2 ^ f) ∣ Nat.card (NativeSporadic.Carrier s)) :
    slmSporadicResidual m f s := by
  have gen : ∀ N : ℕ, Nat.card (NativeSporadic.Carrier s) = N → ¬ 2 ^ 47 ∣ N →
      (∀ m ∈ Finset.range 11, ∀ f ∈ Finset.range 8, 4 ≤ m → 1 ≤ f →
        f * ((m - 1) * m / 2) ≤ 46 → slmSporadicResidual m f s ∨
          ¬ ordA (m - 1) (2 ^ f) ∣ N) →
      slmSporadicResidual m f s :=
    fun N hN h47 hcheck => slmSporadicResidual_of_check hm hf (hN ▸ hdvd) h47 hcheck
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

theorem false_of_sporadic_PSL (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {m f : ℕ} (hm : 4 ≤ m) (hmf : ¬ (m = 4 ∧ f = 1))
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f) : False := by
  obtain ⟨s, ⟨e⟩⟩ := hsp
  by_cases hsM : s = .M
  · subst hsM
    exact false_of_monster_PSL hMinn hMcomp hS hna e hσ (by omega) hD hDm
  have hc := card_of_lieModel_PSL_two hDm
  have hdvd : ordA (m - 1) (2 ^ f) ∣ Nat.card (NativeSporadic.Carrier s) := by
    rw [← hc, ← Nat.card_congr e.toEquiv]
    exact OmegaPilot.card_quotient_center_dvd_card_of_fixed D
  rcases slmSporadicResidual_of_dvd hm (one_le_of_lieModel_PSL hDm) hsM hdvd with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl, hs⟩ | ⟨rfl, rfl, hs⟩ | ⟨rfl, rfl, hs⟩ | ⟨hm56, rfl, rfl⟩
  · exact hmf ⟨rfl, rfl⟩
  ·
    have hv : ordA (4 - 1) (2 ^ 2) = 987033600 := by decide
    rw [hv] at hc
    rcases hs with rfl | rfl | rfl
    · have h11 := OmegaPilot.fi23_eleven_dvd_card_quotient_center hS hna e hσ hD
      rw [hc] at h11
      norm_num at h11
    · rcases OmegaPilot.fi24_card_quotient_center hS hna e hσ hD with h | h | h <;>
        rw [hc] at h <;> norm_num at h
    · rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD with h | h <;>
        rw [hc] at h <;> norm_num at h
  ·
    rcases hs with rfl | rfl | rfl
    · exact OmegaPilot.false_of_j4_component hS hna e hσ hD
    · exact false_of_th_component hS hna e hσ hD
    · have hv : ordA (5 - 1) (2 ^ 1) = 9999360 := by decide
      rw [hv] at hc
      rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD with h | h <;>
        rw [hc] at h <;> norm_num at h
  ·
    rcases hs with rfl | rfl
    · exact false_of_th_component hS hna e hσ hD
    · have hv : ordA (6 - 1) (2 ^ 1) = 20158709760 := by decide
      rw [hv] at hc
      rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD with h | h <;>
        rw [hc] at h <;> norm_num at h
  ·
    have hv : ordA (m - 1) (2 ^ 2) = 258492255436800 ∨
        ordA (m - 1) (2 ^ 2) = 361310134959341568000 := by
      rcases hm56 with rfl | rfl
      · left; decide
      · right; decide
    rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD with h | h <;>
      rcases hv with h' | h' <;> rw [hc, h'] at h <;> norm_num at h

theorem catSLmSporadicAt_of_monster (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {m : ℕ} (hm : 4 ≤ m) : CatSLmSporadicAt m := by
  intro S _ _ hS hna hsp σ hσ f D hD hDm _
  by_cases hmf : m = 4 ∧ f = 1
  · exact ⟨hmf.2, .inr hmf.1⟩
  · exact (false_of_sporadic_PSL hMinn hMcomp hS hna hsp hσ hm hmf hD hDm).elim

end Orders

end CFSG.SeitzReduction.LinearPilot
