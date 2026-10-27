module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersSporadic
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatEvenClassical
public import CFSG.Monster.Existence.Compat.Remaining

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput
  isComponent_map_mulEquiv mulAut_conj_injective_of_simple GLS3OddLieAutComponentsInput)


theorem false_of_monster_E7 (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.M) {σ : MulAut S} (hσ : orderOf σ = 2) {f : ℕ}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) (hD7 : LieModel D .E7 0 2 f) :
    False := by
  have := hS
  obtain ⟨t, rfl⟩ := hMinn S hS ⟨e⟩ σ
  have ht : orderOf t = 2 := by
    rw [← orderOf_injective _ (mulAut_conj_injective_of_simple hna) t]
    exact hσ
  let φ := MulEquiv.subgroupCongr (F4Pilot.fixedSubgroup_conj t)
  have hB := isComponent_map_mulEquiv φ hD
  obtain ⟨-, h42⟩ := hMcomp S hS ⟨e⟩ t ht _ hB
  let eB : D ≃* D.map φ.toMonoidHom := D.equivMapOfInjective φ.toMonoidHom φ.injective
  have hsD : IsSimpleGroup D := isSimpleGroup_of_lieModel_E7 hD7
  have hsB : IsSimpleGroup (D.map φ.toMonoidHom) := eB.symm.isSimpleGroup
  have hZB : center (D.map φ.toMonoidHom) = ⊥ := F4Pilot.center_eq_bot_of_isQuasisimple hB.1 hsB
  have hcard : Nat.card ((D.map φ.toMonoidHom) ⧸ center (D.map φ.toMonoidHom)) = Nat.card D :=
    (Nat.card_congr (F4Pilot.mulEquivCenterQuotient hZB).toEquiv).trans
      (Nat.card_congr eB.symm.toEquiv)
  rw [hcard] at h42
  exact h42 ((pow_dvd_pow 2 (by norm_num : 42 ≤ 63)).trans
    (two_pow_dvd_card_of_lieModel_E7_two hD7))

section Orders


theorem false_of_sporadic_E7 (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S} (hσ : orderOf σ = 2) {f : ℕ}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) (hD7 : LieModel D .E7 0 2 f) :
    False := by
  obtain ⟨s, ⟨e⟩⟩ := hsp
  have hdvdS : Nat.card D ∣ Nat.card S := by
    have h1 : Nat.card (D.map (fixedSubgroup σ).subtype) = Nat.card D :=
      card_map_of_injective (fixedSubgroup σ).subtype_injective
    exact h1 ▸ card_subgroup_dvd_card _
  have h63 : 2 ^ 63 ∣ Nat.card (NativeSporadic.Carrier s) :=
    (two_pow_dvd_card_of_lieModel_E7_two hD7).trans ((Nat.card_congr e.toEquiv) ▸ hdvdS)
  have gen : ∀ N : ℕ, Nat.card (NativeSporadic.Carrier s) = N → ¬ 2 ^ 63 ∣ N → False :=
    fun N hN h => h (hN ▸ h63)
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
  case B => exact gen _ Monster.Existence.card_nativeB (by decide)
  case M => exact false_of_monster_E7 hMinn hMcomp hS hna e hσ hD hD7

theorem catE7Sporadic_of_monster (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) : CatE7Sporadic :=
  fun _ _ _ hS hna hsp _ hσ _ _ hD hD7 _ => false_of_sporadic_E7 hMinn hMcomp hS hna hsp hσ hD hD7

end Orders

end CFSG.SeitzReduction.E8Pilot
