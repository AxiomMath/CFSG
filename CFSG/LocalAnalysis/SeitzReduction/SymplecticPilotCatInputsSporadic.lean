module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDet

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput
  isComponent_map_mulEquiv mulAut_conj_injective_of_simple)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

@[expose] def CatSp2mSporadic (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    NativeSporadic.SporadicRep S → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .PSp m 2 f →
      ((σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D) ∨
        FixedCentralizerTwoFree σ D) → False

@[expose] def sp2mSporadicResidual (m f : ℕ) (s : TauCeti.SporadicName) : Prop :=
  (m = 2 ∧ ((f = 2 ∧ (s = .He ∨ s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B)) ∨
      (f = 3 ∧ (s = .Co1 ∨ s = .Th ∨ s = .Fi24Prime ∨ s = .B)))) ∨
    (m = 3 ∧ F4Pilot.sp6SporadicResidual f s) ∨
    (m = 4 ∧ f = 1 ∧ (s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B)) ∨
    ((m = 5 ∨ m = 6) ∧ f = 1 ∧ s = .B)

instance (m f : ℕ) (s : TauCeti.SporadicName) : Decidable (sp2mSporadicResidual m f s) := by
  unfold sp2mSporadicResidual F4Pilot.sp6SporadicResidual
  infer_instance

theorem sp2mSporadicResidual_three_iff {f : ℕ} {s : TauCeti.SporadicName} :
    sp2mSporadicResidual 3 f s ↔ F4Pilot.sp6SporadicResidual f s := by
  simp [sp2mSporadicResidual]

theorem not_sp2mSporadicResidual {m f : ℕ} {s : TauCeti.SporadicName}
    (h : 7 ≤ m ∨ (4 ≤ m ∧ 2 ≤ f)) : ¬ sp2mSporadicResidual m f s := by
  unfold sp2mSporadicResidual
  omega

@[expose] def CatSp2mSporadicResidual (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ s : TauCeti.SporadicName, Nonempty (S ≃* NativeSporadic.Carrier s) →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      IsComponent D → LieModel D .PSp m 2 f →
      ((σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D) ∨
        FixedCentralizerTwoFree σ D) →
      sp2mSporadicResidual m f s → False

theorem catSp2mSporadicResidual_of_seven_le {m : ℕ} (hm : 7 ≤ m) : CatSp2mSporadicResidual m :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr => not_sp2mSporadicResidual (.inl hm) hr

theorem catSp2mSporadicResidual_three_of_catSp6SporadicResidual
    (h : F4Pilot.CatSp6SporadicResidual) : CatSp2mSporadicResidual 3 := by
  intro S _ _ hS hna s hs σ hσ f D hD hD6 hcase hr
  exact h S hS hna s hs σ hσ f D hD hD6 (hcase.imp And.left id)
    (sp2mSporadicResidual_three_iff.mp hr)

theorem catSp2mSporadic_three_of_catSp6Sporadic (h : F4Pilot.CatSp6Sporadic) :
    CatSp2mSporadic 3 :=
  fun S _ _ hS hna hsp σ hσ f D hD hD6 hcase =>
    h S hS hna hsp σ hσ f D hD hD6 (hcase.imp And.left id)

theorem card_of_lieModel_PSp_eq_two_pow_mul_odd {D : Type} [Group D] {m f : ℕ}
    (h : LieModel D .PSp m 2 f) : ∃ A : ℕ, Odd A ∧ Nat.card D = 2 ^ (f * (m * m)) * A := by
  obtain ⟨hf, -, -⟩ := admissible_of_lieModel_PSp h
  obtain ⟨A, hA, hm⟩ := (Timmesfeld.Orders.profile_ordBC (n := m) hf).two
  exact ⟨A, hA, (card_of_lieModel_PSp_two_pow h).trans hm⟩

theorem mul_mul_self_ne_forty_one {m f : ℕ} (hm : 2 ≤ m) : f * (m * m) ≠ 41 := by
  intro h
  rcases (by omega : m ≤ 6 ∨ 7 ≤ m) with h6 | h7
  · interval_cases m <;> omega
  · have h49 : 7 * 7 ≤ m * m := Nat.mul_le_mul h7 h7
    have hf : 1 ≤ f := by
      by_contra h0
      obtain rfl : f = 0 := by omega
      omega
    have : m * m ≤ f * (m * m) := Nat.le_mul_of_pos_left _ hf
    omega

theorem false_of_monster_sp2m (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.M) {σ : MulAut S} (hσ : orderOf σ = 2) {m f : ℕ}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) (hDm : LieModel D .PSp m 2 f) :
    False := by
  have := hS
  obtain ⟨t, rfl⟩ := hMinn S hS ⟨e⟩ σ
  have ht : orderOf t = 2 := by
    rw [← orderOf_injective _ (mulAut_conj_injective_of_simple hna) t]
    exact hσ
  let φ := MulEquiv.subgroupCongr (F4Pilot.fixedSubgroup_conj t)
  have hB := isComponent_map_mulEquiv φ hD
  obtain ⟨h41, h42⟩ := hMcomp S hS ⟨e⟩ t ht _ hB
  let eB : D ≃* D.map φ.toMonoidHom := D.equivMapOfInjective φ.toMonoidHom φ.injective
  have hsD : IsSimpleGroup D := F4Pilot.isSimpleGroup_of_lieModel_PSp hDm
  have hsB : IsSimpleGroup (D.map φ.toMonoidHom) := eB.symm.isSimpleGroup
  have hZB : center (D.map φ.toMonoidHom) = ⊥ := F4Pilot.center_eq_bot_of_isQuasisimple hB.1 hsB
  have hcard : Nat.card ((D.map φ.toMonoidHom) ⧸ center (D.map φ.toMonoidHom)) = Nat.card D :=
    (Nat.card_congr (F4Pilot.mulEquivCenterQuotient hZB).toEquiv).trans
      (Nat.card_congr eB.symm.toEquiv)
  rw [hcard] at h41 h42
  obtain ⟨A, hA, hDA⟩ := card_of_lieModel_PSp_eq_two_pow_mul_odd hDm
  rw [hDA] at h41 h42
  have h1 := F4Pilot.le_of_two_pow_dvd_two_pow_mul_odd hA h41
  have h2 : f * (m * m) < 42 := by
    by_contra h
    exact h42 ((pow_dvd_pow 2 (by omega)).trans (dvd_mul_right _ _))
  exact mul_mul_self_ne_forty_one (f := f) (admissible_of_lieModel_PSp hDm).2.1 (by omega)

theorem sp2mSporadicResidual_of_check {m f N : ℕ} {s : TauCeti.SporadicName} (hm : 2 ≤ m)
    (hf : 1 ≤ f) (h21 : (m, f) ≠ (2, 1)) (hdvd : Open.ordBC m (2 ^ f) ∣ N)
    (h47 : ¬ 2 ^ 47 ∣ N)
    (hcheck : ∀ m ∈ Finset.range 7, ∀ f ∈ Finset.range 12, 2 ≤ m → 1 ≤ f → (m, f) ≠ (2, 1) →
      f * (m * m) ≤ 46 → sp2mSporadicResidual m f s ∨ ¬ Open.ordBC m (2 ^ f) ∣ N) :
    sp2mSporadicResidual m f s := by
  have h2 : f * (m * m) ≤ 46 := by
    by_contra h
    exact h47 ((Nat.pow_dvd_pow 2 (by omega)).trans ((ordBC_two_pow_bounds hf).1.trans hdvd))
  have hm7 : m < 7 := by
    by_contra h
    have h49 : 7 * 7 ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
    have : m * m ≤ f * (m * m) := Nat.le_mul_of_pos_left _ hf
    omega
  have hf12 : f < 12 := by
    have h4 : 2 * 2 ≤ m * m := Nat.mul_le_mul hm hm
    have : f * (2 * 2) ≤ f * (m * m) := Nat.mul_le_mul_left f h4
    omega
  rcases hcheck m (Finset.mem_range.mpr hm7) f (Finset.mem_range.mpr hf12) hm hf h21 h2 with
    h | h
  · exact h
  · exact absurd hdvd h

section Orders


theorem sp2mSporadicResidual_of_dvd {m f : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f) (h21 : (m, f) ≠ (2, 1))
    {s : TauCeti.SporadicName} (hs : s ≠ .M)
    (hdvd : Open.ordBC m (2 ^ f) ∣ Nat.card (NativeSporadic.Carrier s)) :
    sp2mSporadicResidual m f s := by
  have gen : ∀ N : ℕ, Nat.card (NativeSporadic.Carrier s) = N → ¬ 2 ^ 47 ∣ N →
      (∀ m ∈ Finset.range 7, ∀ f ∈ Finset.range 12, 2 ≤ m → 1 ≤ f → (m, f) ≠ (2, 1) →
        f * (m * m) ≤ 46 → sp2mSporadicResidual m f s ∨ ¬ Open.ordBC m (2 ^ f) ∣ N) →
      sp2mSporadicResidual m f s :=
    fun N hN h47 hcheck => sp2mSporadicResidual_of_check hm hf h21 (hN ▸ hdvd) h47 hcheck
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

theorem catSp2mSporadic_of_residual (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {m : ℕ} (hres : CatSp2mSporadicResidual m) :
    CatSp2mSporadic m := by
  intro S _ _ hS hna ⟨s, ⟨e⟩⟩ σ hσ f D hD hDm hcase
  by_cases hsM : s = .M
  · subst hsM
    exact false_of_monster_sp2m hMinn hMcomp hS hna e hσ hD hDm
  obtain ⟨hf, hm, h22⟩ := admissible_of_lieModel_PSp hDm
  have hdvdS : Nat.card D ∣ Nat.card S := by
    have h1 : Nat.card (D.map (fixedSubgroup σ).subtype) = Nat.card D :=
      card_map_of_injective (fixedSubgroup σ).subtype_injective
    exact h1 ▸ card_subgroup_dvd_card _
  have hdvd : Open.ordBC m (2 ^ f) ∣ Nat.card (NativeSporadic.Carrier s) := by
    rw [← card_of_lieModel_PSp_two_pow hDm, ← Nat.card_congr e.toEquiv]
    exact hdvdS
  have h21 : (m, f) ≠ (2, 1) := by
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact h22 rfl
  exact hres S hS hna s ⟨e⟩ σ hσ f D hD hDm hcase
    (sp2mSporadicResidual_of_dvd hm hf h21 hsM hdvd)

theorem catSp2mSporadic_of_seven_le (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {m : ℕ} (hm : 7 ≤ m) : CatSp2mSporadic m :=
  catSp2mSporadic_of_residual hMinn hMcomp (catSp2mSporadicResidual_of_seven_le hm)

end Orders

end CFSG.SeitzReduction.SymplecticPilot
