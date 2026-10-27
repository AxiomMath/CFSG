module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatU6Sporadic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput
  isComponent_map_mulEquiv mulAut_conj_injective_of_simple)

theorem exists_odd_evenLieOrder_POmega_four_eq {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {f : ℕ} (hf : 1 ≤ f) :
    ∃ r, Odd r ∧ F4Pilot.evenLieOrder t 4 f = 2 ^ (12 * f) * r := by
  have h12 : f * (4 * (4 - 1)) = 12 * f := by
    rw [show 4 * (4 - 1) = 12 from rfl, mul_comm]
  rcases ht with rfl | rfl
  · obtain ⟨r, hr, h⟩ := (Timmesfeld.Orders.profile_ordD (n := 4) (f := f) (by norm_num) hf).two
    exact ⟨r, hr, by rw [show F4Pilot.evenLieOrder .POmegaPlus 4 f = ordD 4 (2 ^ f) from rfl, h,
      h12]⟩
  · obtain ⟨r, hr, h⟩ :=
      (Timmesfeld.Orders.profile_ordTwistedD (n := 4) (f := f) (by norm_num) hf).two
    exact ⟨r, hr, by
      rw [show F4Pilot.evenLieOrder .POmegaMinus 4 f = ordTwistedD 4 (2 ^ f) from rfl, h, h12]⟩

theorem two_pow_dvd_evenLieOrder_POmega_four {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {f k : ℕ} (hf : 1 ≤ f) (hk : k ≤ 12 * f) :
    2 ^ k ∣ F4Pilot.evenLieOrder t 4 f := by
  obtain ⟨r, -, h⟩ := exists_odd_evenLieOrder_POmega_four_eq ht hf
  rw [h]
  exact (pow_dvd_pow 2 hk).trans (dvd_mul_right _ _)

theorem sq_seventeen_dvd_ordD_four_four : 17 ^ 2 ∣ ordD 4 (2 ^ 2) := by decide

theorem two_five_seven_dvd_ordTwistedD_four_four : 257 ∣ ordTwistedD 4 (2 ^ 2) := by decide

theorem seventy_three_dvd_ordD_four_eight : 73 ∣ ordD 4 (2 ^ 3) := by decide

theorem seventy_three_dvd_ordTwistedD_four_eight : 73 ∣ ordTwistedD 4 (2 ^ 3) := by decide

theorem false_of_monster_POmega_four (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M) {σ : MulAut S}
    (hσ : orderOf σ = 2) {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {f : ℕ}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) t 4 2 f) : False := by
  have hf : 1 ≤ f := OmegaPilot.one_le_of_lieModel_POmega ht hDm
  have := hS
  obtain ⟨u, rfl⟩ := hMinn S hS ⟨e⟩ σ
  have hu : orderOf u = 2 := by
    rw [← orderOf_injective _ (mulAut_conj_injective_of_simple hna) u]
    exact hσ
  let φ := MulEquiv.subgroupCongr (F4Pilot.fixedSubgroup_conj u)
  have hB := isComponent_map_mulEquiv φ hD
  obtain ⟨h41, h42⟩ := hMcomp S hS ⟨e⟩ u hu _ hB
  let eB : D ≃* D.map φ.toMonoidHom := D.equivMapOfInjective φ.toMonoidHom φ.injective
  rw [← card_quotient_center_eq_of_mulEquiv eB, OmegaPilot.card_of_lieModel_POmega_two ht hDm]
    at h41 h42
  obtain ⟨r, hr, hO⟩ := exists_odd_evenLieOrder_POmega_four_eq ht hf
  rw [hO] at h41 h42
  have h1 := F4Pilot.le_of_two_pow_dvd_two_pow_mul_odd hr h41
  have h2 : 12 * f < 42 := by
    by_contra h
    exact h42 ((pow_dvd_pow 2 (by omega)).trans (dvd_mul_right _ _))
  omega

section Orders


theorem exists_dvd_evenLieOrder_POmega_four_not_dvd_B {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {f : ℕ} (hf2 : 2 ≤ f) (hf3 : f ≤ 3) :
    ∃ n : ℕ, n ∣ F4Pilot.evenLieOrder t 4 f ∧ ¬ n ∣ Open.monsterBabyOrder := by
  rcases (by omega : f = 2 ∨ f = 3) with rfl | rfl <;> rcases ht with rfl | rfl
  · exact ⟨17 ^ 2, sq_seventeen_dvd_ordD_four_four, by decide⟩
  · exact ⟨257, two_five_seven_dvd_ordTwistedD_four_four, by decide⟩
  · exact ⟨73, seventy_three_dvd_ordD_four_eight, by decide⟩
  · exact ⟨73, seventy_three_dvd_ordTwistedD_four_eight, by decide⟩

theorem false_of_sporadic_POmega_four_of_two_le (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {f : ℕ}
    (hf : 2 ≤ f) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) t 4 2 f) : False := by
  obtain ⟨s, ⟨e⟩⟩ := hsp
  have hdvdS : Nat.card (D ⧸ center D) ∣ Nat.card S := by
    have h1 : Nat.card (D.map (fixedSubgroup σ).subtype) = Nat.card D :=
      card_map_of_injective (fixedSubgroup σ).subtype_injective
    exact (card_quotient_dvd_card _).trans (h1 ▸ card_subgroup_dvd_card _)
  have hdvd : F4Pilot.evenLieOrder t 4 f ∣ Nat.card (NativeSporadic.Carrier s) := by
    rw [← OmegaPilot.card_of_lieModel_POmega_two ht hDm, ← Nat.card_congr e.toEquiv]
    exact hdvdS
  have h2pow : ∀ k, k ≤ 12 * f → 2 ^ k ∣ Nat.card (NativeSporadic.Carrier s) := fun k hk =>
    (two_pow_dvd_evenLieOrder_POmega_four ht (by omega) hk).trans hdvd
  have gen : ∀ N : ℕ, Nat.card (NativeSporadic.Carrier s) = N → ¬ 2 ^ 24 ∣ N → False :=
    fun N hN h => h (hN ▸ h2pow 24 (by omega))
  cases s
  case M11 => exact gen _ Sporadic.Mathieu.card_M11 (by decide)
  case M12 => exact gen _ Sporadic.Mathieu.card_M12 (by decide)
  case M22 => exact gen _ Sporadic.Mathieu.card_M22 (by decide)
  case M23 => exact gen _ EvenSmallLie.CatalogOrders.card_M23 (by decide)
  case M24 => exact gen _ Sporadic.Mathieu.card_M24 (by decide)
  case J1 => exact gen _ Sporadic.J1.card_J1 (by decide)
  case J2 => exact gen _ Sporadic.J2.card_J2 (by decide)
  case J3 => exact gen _ Sporadic.J3.card_J3 (by decide)
  case J4 => exact gen _ Sporadic.J4.card_J4 (by decide)
  case HS => exact gen _ Sporadic.HS.card_HS (by decide)
  case McL => exact gen _ Sporadic.McL.card_McL (by decide)
  case He => exact gen _ Sporadic.He.fam_he_order.1 (by decide)
  case Ru => exact gen _ Sporadic.Ru.card_Ru (by decide)
  case Ly => exact gen _ Sporadic.Ly.card_Ly (by decide)
  case Suz => exact gen _ Sporadic.Suz.card_Suz (by decide)
  case ONan => exact gen _ Sporadic.ON.card_ON (by decide)
  case Co1 => exact gen _ Sporadic.Co1.card_Co1 (by decide)
  case Co2 => exact gen _ Sporadic.Co2.card_Co2 (by decide)
  case Co3 => exact gen _ Sporadic.Co3.card_Co3 (by decide)
  case Fi22 => exact gen _ Sporadic.Fi22.card_Fi22 (by decide)
  case Fi23 => exact gen _ Sporadic.Fi23.card_Fi23 (by decide)
  case Fi24Prime => exact gen _ Sporadic.Fi24.card_Fi24prime (by decide)
  case HN => exact gen _ Sporadic.HN.card_HN (by decide)
  case Th => exact gen _ Monster.Existence.Compat.card_nativeTh (by decide)
  case B =>
    have hB : Nat.card (NativeSporadic.Carrier .B) = Open.monsterBabyOrder :=
      Monster.Existence.card_nativeB
    rcases (by omega : f ≤ 3 ∨ 4 ≤ f) with h3 | h4
    · obtain ⟨n, hn, hnB⟩ := exists_dvd_evenLieOrder_POmega_four_not_dvd_B ht hf h3
      exact hnB (hB ▸ hn.trans hdvd)
    · have h48 := h2pow 48 (by omega)
      rw [hB] at h48
      revert h48
      decide
  case M => exact false_of_monster_POmega_four hMinn hMcomp hS hna e hσ ht hD hDm

end Orders

end CFSG.SeitzReduction.TwistedE6Pilot
