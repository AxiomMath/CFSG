module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatOdd
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersSporadic
public import CFSG.Monster.Existence.Compat.Remaining

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput
  isComponent_map_mulEquiv mulAut_conj_injective_of_simple)

theorem card_of_lieModel_PSp_three_two_eq_two_pow_mul_odd {D : Type} [Group D] {f : ℕ}
    (h : LieModel D .PSp 3 2 f) : ∃ A : ℕ, Odd A ∧ Nat.card D = 2 ^ (9 * f) * A := by
  have hf : 1 ≤ f := (statedClassicalModel_of_lieModel_psp h).1.2.1
  have hodd : ∀ k : ℕ, 1 ≤ k → Odd ((2 ^ f) ^ k - 1) := fun k hk =>
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity))
      (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by omega⟩) odd_one
  refine ⟨_, ((hodd 2 (by norm_num)).mul (hodd 4 (by norm_num))).mul (hodd 6 (by norm_num)), ?_⟩
  rw [card_of_lieModel_PSp_three_two h, ← pow_mul, mul_comm f 9]

theorem le_of_two_pow_dvd_two_pow_mul_odd {a b A : ℕ} (hA : Odd A) (h : 2 ^ a ∣ 2 ^ b * A) :
    a ≤ b := by
  by_contra hlt
  have h1 : 2 ^ (b + 1) ∣ 2 ^ b * A := (pow_dvd_pow 2 (by omega)).trans h
  rw [pow_succ] at h1
  have h2 := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ b)).mp h1
  exact (Nat.not_even_iff_odd.mpr hA) (even_iff_two_dvd.mpr h2)

theorem false_of_monster (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.M) {σ : MulAut S} (hσ : orderOf σ = 2) {f : ℕ}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) (hD6 : LieModel D .PSp 3 2 f) :
    False := by
  have := hS
  obtain ⟨t, rfl⟩ := hMinn S hS ⟨e⟩ σ
  have ht : orderOf t = 2 := by
    rw [← orderOf_injective _ (mulAut_conj_injective_of_simple hna) t]
    exact hσ
  let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj t)
  have hB := isComponent_map_mulEquiv φ hD
  obtain ⟨h41, h42⟩ := hMcomp S hS ⟨e⟩ t ht _ hB
  let eB : D ≃* D.map φ.toMonoidHom := D.equivMapOfInjective φ.toMonoidHom φ.injective
  have hsD : IsSimpleGroup D := isSimpleGroup_of_lieModel_PSp hD6
  have hsB : IsSimpleGroup (D.map φ.toMonoidHom) := eB.symm.isSimpleGroup
  have hZB : center (D.map φ.toMonoidHom) = ⊥ := center_eq_bot_of_isQuasisimple hB.1 hsB
  have hcard : Nat.card ((D.map φ.toMonoidHom) ⧸ center (D.map φ.toMonoidHom)) = Nat.card D :=
    (Nat.card_congr (mulEquivCenterQuotient hZB).toEquiv).trans (Nat.card_congr eB.symm.toEquiv)
  rw [hcard] at h41 h42
  obtain ⟨A, hA, hDA⟩ := card_of_lieModel_PSp_three_two_eq_two_pow_mul_odd hD6
  rw [hDA] at h41 h42
  have h1 := le_of_two_pow_dvd_two_pow_mul_odd hA h41
  have h2 : 9 * f < 42 := by
    by_contra h
    exact h42 ((pow_dvd_pow 2 (by omega)).trans (dvd_mul_right _ _))
  omega

@[expose] def sp6SporadicResidual (f : ℕ) (s : TauCeti.SporadicName) : Prop :=
  (f = 1 ∧ (s = .Suz ∨ s = .ONan ∨ s = .Co1 ∨ s = .Co2 ∨ s = .Co3 ∨ s = .Fi22 ∨ s = .Fi23 ∨
    s = .Fi24Prime ∨ s = .HN ∨ s = .Th ∨ s = .B)) ∨ (f = 2 ∧ s = .B)

@[expose] def CatSp6SporadicResidual : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ s : TauCeti.SporadicName, Nonempty (S ≃* NativeSporadic.Carrier s) →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      IsComponent D → LieModel D .PSp 3 2 f →
      (σ ∈ (MulAut.conj : S →* MulAut S).range ∨ FixedCentralizerTwoFree σ D) →
      sp6SporadicResidual f s → False

section Orders


theorem catSp6Sporadic_of_residual (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : CatSp6SporadicResidual) : CatSp6Sporadic := by
  intro S _ _ hS hna ⟨s, ⟨e⟩⟩ σ hσ f D hD hD6 hcase
  by_cases hr : sp6SporadicResidual f s
  · exact hres S hS hna s ⟨e⟩ σ hσ f D hD hD6 hcase hr
  have hf : 1 ≤ f := (statedClassicalModel_of_lieModel_psp hD6).1.2.1
  have hdvdS : Nat.card D ∣ Nat.card S := by
    have h1 : Nat.card (D.map (fixedSubgroup σ).subtype) = Nat.card D :=
      card_map_of_injective (fixedSubgroup σ).subtype_injective
    exact h1 ▸ card_subgroup_dvd_card _
  have hdvd : Nat.card D ∣ Nat.card (NativeSporadic.Carrier s) :=
    (Nat.card_congr e.toEquiv) ▸ hdvdS
  have hd1 : f = 1 → Nat.card D = 1451520 := by
    rintro rfl
    rw [card_of_lieModel_PSp_three_two hD6]
    norm_num
  have hd2 : f = 2 → Nat.card D = 4106059776000 := by
    rintro rfl
    rw [card_of_lieModel_PSp_three_two hD6]
    norm_num
  have hd3 : ∀ k : ℕ, k ≤ 9 * f → 2 ^ k ∣ Nat.card D := by
    intro k hk
    obtain ⟨A, -, hA⟩ := card_of_lieModel_PSp_three_two_eq_two_pow_mul_odd hD6
    rw [hA]
    exact (pow_dvd_pow 2 hk).trans (dvd_mul_right _ _)
  have gen : ∀ N : ℕ, Nat.card (NativeSporadic.Carrier s) = N → ¬ 2 ^ 27 ∣ N →
      ¬ 4106059776000 ∣ N → (f = 1 → ¬ 1451520 ∣ N) → False := by
    intro N hN h27 h4 h1
    rw [hN] at hdvd
    rcases (by omega : f = 1 ∨ f = 2 ∨ 3 ≤ f) with h | h | h
    · exact h1 h (hd1 h ▸ hdvd)
    · exact h4 (hd2 h ▸ hdvd)
    · exact h27 ((hd3 27 (by omega)).trans hdvd)
  cases s
  case M11 => exact gen _ Sporadic.Mathieu.card_M11 (by decide) (by decide) (fun _ => by decide)
  case M12 => exact gen _ Sporadic.Mathieu.card_M12 (by decide) (by decide) (fun _ => by decide)
  case M22 => exact gen _ Sporadic.Mathieu.card_M22 (by decide) (by decide) (fun _ => by decide)
  case M23 =>
    exact gen _ EvenSmallLie.CatalogOrders.card_M23 (by decide) (by decide) (fun _ => by decide)
  case M24 => exact gen _ Sporadic.Mathieu.card_M24 (by decide) (by decide) (fun _ => by decide)
  case J1 => exact gen _ Sporadic.J1.card_J1 (by decide) (by decide) (fun _ => by decide)
  case J2 => exact gen _ Sporadic.J2.card_J2 (by decide) (by decide) (fun _ => by decide)
  case J3 => exact gen _ Sporadic.J3.card_J3 (by decide) (by decide) (fun _ => by decide)
  case J4 => exact gen _ Sporadic.J4.card_J4 (by decide) (by decide) (fun _ => by decide)
  case HS => exact gen _ Sporadic.HS.card_HS (by decide) (by decide) (fun _ => by decide)
  case McL => exact gen _ Sporadic.McL.card_McL (by decide) (by decide) (fun _ => by decide)
  case He => exact gen _ Sporadic.He.fam_he_order.1 (by decide) (by decide) (fun _ => by decide)
  case Ru => exact gen _ Sporadic.Ru.card_Ru (by decide) (by decide) (fun _ => by decide)
  case Ly => exact gen _ Sporadic.Ly.card_Ly (by decide) (by decide) (fun _ => by decide)
  case Suz => exact gen _ Sporadic.Suz.card_Suz (by decide) (by decide) (fun h => (hr (Or.inl ⟨h, by simp⟩)).elim)
  case ONan => exact gen _ Sporadic.ON.card_ON (by decide) (by decide) (fun h => (hr (Or.inl ⟨h, by simp⟩)).elim)
  case Co1 => exact gen _ Sporadic.Co1.card_Co1 (by decide) (by decide) (fun h => (hr (Or.inl ⟨h, by simp⟩)).elim)
  case Co2 => exact gen _ Sporadic.Co2.card_Co2 (by decide) (by decide) (fun h => (hr (Or.inl ⟨h, by simp⟩)).elim)
  case Co3 => exact gen _ Sporadic.Co3.card_Co3 (by decide) (by decide) (fun h => (hr (Or.inl ⟨h, by simp⟩)).elim)
  case Fi22 => exact gen _ Sporadic.Fi22.card_Fi22 (by decide) (by decide) (fun h => (hr (Or.inl ⟨h, by simp⟩)).elim)
  case Fi23 => exact gen _ Sporadic.Fi23.card_Fi23 (by decide) (by decide) (fun h => (hr (Or.inl ⟨h, by simp⟩)).elim)
  case Fi24Prime =>
    exact gen _ Sporadic.Fi24.card_Fi24prime (by decide) (by decide) (fun h => (hr (Or.inl ⟨h, by simp⟩)).elim)
  case HN => exact gen _ Sporadic.HN.card_HN (by decide) (by decide) (fun h => (hr (Or.inl ⟨h, by simp⟩)).elim)
  case Th =>
    exact gen _ Monster.Existence.Compat.card_nativeTh (by decide) (by decide) (fun h => (hr (Or.inl ⟨h, by simp⟩)).elim)
  case B =>
    have hB : Nat.card (NativeSporadic.Carrier .B) = Open.monsterBabyOrder :=
      Monster.Existence.card_nativeB
    rw [hB] at hdvd
    have hr1 : f ≠ 1 := fun h1 => hr (Or.inl ⟨h1, by simp⟩)
    have hr2 : f ≠ 2 := fun h2 => hr (Or.inr ⟨h2, rfl⟩)
    rcases (by omega : f = 3 ∨ f = 4 ∨ 5 ≤ f) with rfl | rfl | h5
    · rw [card_of_lieModel_PSp_three_two hD6] at hdvd
      revert hdvd
      decide
    · rw [card_of_lieModel_PSp_three_two hD6] at hdvd
      revert hdvd
      decide
    · have h45 := (hd3 45 (by omega)).trans hdvd
      revert h45
      decide
  case M => exact false_of_monster hMinn hMcomp hS hna e hσ hD hD6

end Orders

end CFSG.SeitzReduction.F4Pilot
