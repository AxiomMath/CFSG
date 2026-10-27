module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicFour
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatSporadic
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSym
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34He
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34Suz
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34ON
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34McL
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34HS
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (ordA)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

@[expose] def SuzOuterL34Input : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* NativeSporadic.Suz) →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
      Nat.card (fixedSubgroup σ) = 1209600 → ∀ D : Subgroup (fixedSubgroup σ), IsComponent D →
        FixedCentralizerTwoFree σ D → ¬ LieModel (D ⧸ center D) .PSL 3 2 2

@[expose] def ONOuterL34Input : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* NativeSporadic.ON) →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
      ∀ D : Subgroup (fixedSubgroup σ), IsComponent D → FixedCentralizerTwoFree σ D →
        ¬ LieModel (D ⧸ center D) .PSL 3 2 2

@[expose] def sl3SporadicResidual (f : ℕ) (s : TauCeti.SporadicName) : Prop :=
  f = 1 ∨ (f = 2 ∧ s ≠ .M11 ∧ s ≠ .M12 ∧ s ≠ .J1 ∧ s ≠ .J3) ∨
    (f = 4 ∧ (s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B))

instance (f : ℕ) (s : TauCeti.SporadicName) : Decidable (sl3SporadicResidual f s) := by
  unfold sl3SporadicResidual
  infer_instance

theorem sl3SporadicResidual_of_check {f N : ℕ} {s : TauCeti.SporadicName} (hf : 1 ≤ f)
    (hdvd : ordA 2 (2 ^ f) ∣ N) (h47 : ¬ 2 ^ 47 ∣ N)
    (hcheck : ∀ f ∈ Finset.range 16, 1 ≤ f → sl3SporadicResidual f s ∨ ¬ ordA 2 (2 ^ f) ∣ N) :
    sl3SporadicResidual f s := by
  have hb := (ordA_two_pow_bounds (n := 2) (by norm_num) hf).1
  have h3 : f * (2 * (2 + 1) / 2) ≤ 46 := by
    by_contra h
    exact h47 ((Nat.pow_dvd_pow 2 (by omega)).trans (hb.trans hdvd))
  rcases hcheck f (Finset.mem_range.mpr (by omega)) hf with h | h
  · exact h
  · exact absurd hdvd h

section Orders

theorem sl3SporadicResidual_of_dvd {f : ℕ} (hf : 1 ≤ f) {s : TauCeti.SporadicName}
    (hs : s ≠ .M) (hdvd : ordA 2 (2 ^ f) ∣ Nat.card (NativeSporadic.Carrier s)) :
    sl3SporadicResidual f s := by
  have gen : ∀ N : ℕ, Nat.card (NativeSporadic.Carrier s) = N → ¬ 2 ^ 47 ∣ N →
      (∀ f ∈ Finset.range 16, 1 ≤ f → sl3SporadicResidual f s ∨ ¬ ordA 2 (2 ^ f) ∣ N) →
      sl3SporadicResidual f s :=
    fun N hN h47 hcheck => sl3SporadicResidual_of_check hf (hN ▸ hdvd) h47 hcheck
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

theorem false_of_sporadic_PSL_three_sixteen {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {s : TauCeti.SporadicName}
    (hs : s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B) (e : S ≃* NativeSporadic.Carrier s)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 1425715200) : False := by
  rcases hs with rfl | rfl | rfl
  · have h := OmegaPilot.fi23_eleven_dvd_card_quotient_center hS hna e hσ hD
    rw [hcard] at h
    norm_num at h
  · rcases OmegaPilot.fi24_card_quotient_center hS hna e hσ hD with h | h | h <;>
      rw [hcard] at h <;> norm_num at h
  · rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD with h | h <;>
      rw [hcard] at h <;> norm_num at h

theorem hn_false_of_card_twenty_thousand {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.HN) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 20160) : False := by
  rcases ComponentClassification.CatLeaf.exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
  · obtain ⟨B, hB, hcardB⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
    have h := ComponentClassification.RestrictedStd.Spor.hnLocalComponentsInput_holds S e u
      (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB
    rw [hcardB, hcard] at h
    norm_num at h
  · have h := SporadicRefine.hn_outer_card_quotient_center e hσ hout hD
    rw [hcard] at h
    norm_num at h

theorem on_false_of_l34 (hON : ONOuterL34Input) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.ON)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 2)
    (hσD : (σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D) ∨
      FixedCentralizerTwoFree σ D) : False := by
  have := hS
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨u, rfl⟩ := hin
    have hu := SporadicRefine.orderOf_eq_two_of_conj_of_simple hS hna hσ
    rcases hσD with ⟨-, hsmall⟩ | hfree
    · exact SporadicRefine.on_inner_not_twoSmall e hu hD hsmall
    · exact not_mem_range_conj_of_twoFree hna hσ hfree ⟨u, rfl⟩
  · exact hON S ⟨e⟩ σ hσ hin D hD (hσD.resolve_left fun h => hin h.1) hDm

theorem suz_false_of_l34 (hSuz : SuzOuterL34Input) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Suz)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 2)
    (hσD : (σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D) ∨
      FixedCentralizerTwoFree σ D) : False := by
  have hcard : Nat.card (D ⧸ center D) = 20160 := by
    rw [card_of_lieModel_PSL_two hDm]
    decide
  obtain ⟨hout, hC⟩ := SporadicRefine.suz_l34_outer_card hS hna e hσ hD hcard hσD
  exact hSuz S ⟨e⟩ σ hσ hout hC D hD (hσD.resolve_left fun h => hout h.1) hDm

theorem false_of_sporadic_PSL_three_of_inputs (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hSuz : SuzOuterL34Input) (hON : ONOuterL34Input)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S} (hσ : orderOf σ = 2) {f : ℕ}
    (hf : f ≠ 1) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 f)
    (hσD : (σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D) ∨
      FixedCentralizerTwoFree σ D) : False := by
  obtain ⟨s, ⟨e⟩⟩ := hsp
  by_cases hsM : s = .M
  · subst hsM
    exact false_of_monster_PSL hMinn hMcomp hS hna e hσ le_rfl hD hDm
  have hc : Nat.card (D ⧸ center D) = ordA 2 (2 ^ f) := card_of_lieModel_PSL_two hDm
  have hdvd : ordA 2 (2 ^ f) ∣ Nat.card (NativeSporadic.Carrier s) := by
    rw [← hc, ← Nat.card_congr e.toEquiv]
    exact OmegaPilot.card_quotient_center_dvd_card_of_fixed D
  rcases sl3SporadicResidual_of_dvd (one_le_of_lieModel_PSL hDm) hsM hdvd with
    h1 | ⟨rfl, h11, h12, hJ1, hJ3⟩ | ⟨rfl, hs⟩
  · exact hf h1
  ·
    have hcard : Nat.card (D ⧸ center D) = 20160 := by
      rw [hc]
      decide
    cases s
    case M11 => exact h11 rfl
    case M12 => exact h12 rfl
    case J1 => exact hJ1 rfl
    case J3 => exact hJ3 rfl
    case M => exact hsM rfl
    case M22 => exact SporadicRefine.m22_false_of_l34 hS hna e hσ hD hcard
    case M23 => exact SporadicRefine.m23_false_of_l34 hS hna e hσ hD hcard
    case M24 => exact SporadicRefine.m24_false_of_l34 hS hna e hσ hD hcard
    case J2 => exact SporadicRefine.j2_false_of_l34 e hσ hcard
    case J4 => exact OmegaPilot.false_of_j4_component hS hna e hσ hD
    case HS => exact SporadicRefine.hs_false_of_l34 e hσ hD hDm
    case McL => exact SporadicRefine.mcl_false_of_l34 hS hna e hσ hD hDm
    case He => exact SporadicRefine.he_false_of_l34 hS hna e hσ hD hcard hσD
    case Ru => exact SporadicRefine.ru_false_of_l34 hS hna e hσ hD hcard
    case Suz => exact suz_false_of_l34 hSuz hS hna e hσ hD hDm hσD
    case ONan => exact on_false_of_l34 hON hS hna e hσ hD hDm hσD
    case Co1 =>
      have h := UnitaryPilot.co1_fixed_card_quotient hS hna e hσ hD
      rw [hcard] at h
      norm_num at h
    case Co2 => exact UnitaryPilot.co2_false_of_fixed_component hS hna e hσ hD
    case Co3 =>
      rcases UnitaryPilot.co3_fixed_card_quotient hS hna e hσ hD with h | h <;>
        rw [hcard] at h <;> norm_num at h
    case Fi22 =>
      obtain ⟨hin, hout⟩ := UnitaryPilot.fi22_fixed_card_quotient hS hna e hσ hD
      by_cases h : σ ∈ (MulAut.conj : S →* MulAut S).range
      · have h' := (hin h).1
        rw [hcard] at h'
        norm_num at h'
      · rcases hout h with h' | h' <;> rw [hcard] at h' <;> norm_num at h'
    case Fi23 =>
      have h := OmegaPilot.fi23_eleven_dvd_card_quotient_center hS hna e hσ hD
      rw [hcard] at h
      norm_num at h
    case Fi24Prime =>
      rcases OmegaPilot.fi24_card_quotient_center hS hna e hσ hD with h | h | h <;>
        rw [hcard] at h <;> norm_num at h
    case HN => exact hn_false_of_card_twenty_thousand hS hna e hσ hD hcard
    case Ly => exact SporadicRefine.ly_false_of_l34 hS hna e hσ hD hcard
    case Th => exact false_of_th_component hS hna e hσ hD
    case B =>
      rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD with h | h <;>
        rw [hcard] at h <;> norm_num at h
  ·
    have hcard : Nat.card (D ⧸ center D) = 1425715200 := by
      rw [hc]
      decide
    exact false_of_sporadic_PSL_three_sixteen hS hna hs e hσ hD hcard

theorem catSLmSporadicAt_three_of_inputs (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hSuz : SuzOuterL34Input) (hON : ONOuterL34Input) :
    CatSLmSporadicAt 3 := by
  intro S _ _ hS hna hsp σ hσ f D hD hDm hσD
  by_cases hf : f = 1
  · exact ⟨hf, .inl rfl⟩
  · exact (false_of_sporadic_PSL_three_of_inputs hMinn hMcomp hSuz hON hS hna hsp hσ hf hD hDm
      hσD).elim

end Orders

end CFSG.SeitzReduction.LinearPilot
