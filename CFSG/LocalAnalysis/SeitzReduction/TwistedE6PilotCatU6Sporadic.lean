module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput
  isComponent_map_mulEquiv mulAut_conj_injective_of_simple)

theorem exists_odd_ordTwistedA_five_eq {f : ℕ} (hf : 1 ≤ f) :
    ∃ r, Odd r ∧ ordTwistedA 5 (2 ^ f) = 2 ^ (15 * f) * r := by
  obtain ⟨r, hr, h⟩ :=
    (Timmesfeld.Orders.profile_ordTwistedA (n := 5) (g := f) (by norm_num) hf).two
  have h15 : f * (5 * (5 + 1) / 2) = 15 * f := by
    rw [show 5 * (5 + 1) / 2 = 15 from rfl, mul_comm]
  exact ⟨r, hr, by rw [h, h15]⟩

theorem two_pow_dvd_ordTwistedA_five {f k : ℕ} (hf : 1 ≤ f) (hk : k ≤ 15 * f) :
    2 ^ k ∣ ordTwistedA 5 (2 ^ f) := by
  obtain ⟨r, -, h⟩ := exists_odd_ordTwistedA_five_eq hf
  rw [h]
  exact (pow_dvd_pow 2 hk).trans (dvd_mul_right _ _)

theorem forty_one_dvd_ordTwistedA_five_four : 41 ∣ ordTwistedA 5 (2 ^ 2) := by decide

theorem card_quotient_center_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ center A) = Nat.card (B ⧸ center B) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (map_center_eq e)).toEquiv

theorem false_of_monster_PSU_six (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M) {σ : MulAut S}
    (hσ : orderOf σ = 2) {f : ℕ} {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSU 6 2 f) : False := by
  have hf : 1 ≤ f := (UnitaryPilot.admissible_of_lieModel_PSU hDm).1
  have := hS
  obtain ⟨t, rfl⟩ := hMinn S hS ⟨e⟩ σ
  have ht : orderOf t = 2 := by
    rw [← orderOf_injective _ (mulAut_conj_injective_of_simple hna) t]
    exact hσ
  let φ := MulEquiv.subgroupCongr (F4Pilot.fixedSubgroup_conj t)
  have hB := isComponent_map_mulEquiv φ hD
  obtain ⟨h41, h42⟩ := hMcomp S hS ⟨e⟩ t ht _ hB
  let eB : D ≃* D.map φ.toMonoidHom := D.equivMapOfInjective φ.toMonoidHom φ.injective
  rw [← card_quotient_center_eq_of_mulEquiv eB, card_of_lieModel_PSU_six_two hDm] at h41 h42
  obtain ⟨r, hr, hU⟩ := exists_odd_ordTwistedA_five_eq hf
  rw [hU] at h41 h42
  have h1 := F4Pilot.le_of_two_pow_dvd_two_pow_mul_odd hr h41
  have h2 : 15 * f < 42 := by
    by_contra h
    exact h42 ((pow_dvd_pow 2 (by omega)).trans (dvd_mul_right _ _))
  omega

section Orders


theorem false_of_sporadic_PSU_six_of_two_le (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {f : ℕ} (hf : 2 ≤ f) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) .PSU 6 2 f) : False := by
  obtain ⟨s, ⟨e⟩⟩ := hsp
  have hdvdS : Nat.card (D ⧸ center D) ∣ Nat.card S := by
    have h1 : Nat.card (D.map (fixedSubgroup σ).subtype) = Nat.card D :=
      card_map_of_injective (fixedSubgroup σ).subtype_injective
    exact (card_quotient_dvd_card _).trans (h1 ▸ card_subgroup_dvd_card _)
  have hdvd : ordTwistedA 5 (2 ^ f) ∣ Nat.card (NativeSporadic.Carrier s) := by
    rw [← card_of_lieModel_PSU_six_two hDm, ← Nat.card_congr e.toEquiv]
    exact hdvdS
  have h2pow : ∀ k, k ≤ 15 * f → 2 ^ k ∣ Nat.card (NativeSporadic.Carrier s) := fun k hk =>
    (two_pow_dvd_ordTwistedA_five (by omega) hk).trans hdvd
  have gen : ∀ N : ℕ, Nat.card (NativeSporadic.Carrier s) = N → ¬ 2 ^ 30 ∣ N → False :=
    fun N hN h => h (hN ▸ h2pow 30 (by omega))
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
    rcases (by omega : f = 2 ∨ 3 ≤ f) with rfl | h3
    · have h41 := forty_one_dvd_ordTwistedA_five_four.trans hdvd
      rw [hB] at h41
      revert h41
      decide
    · have h45 := h2pow 45 (by omega)
      rw [hB] at h45
      revert h45
      decide
  case M => exact false_of_monster_PSU_six hMinn hMcomp hS hna e hσ hD hDm

end Orders

end CFSG.SeitzReduction.TwistedE6Pilot
