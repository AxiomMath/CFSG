module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatEvenOuter
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterPSL

public noncomputable section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (SpFixedOrNoPComponent psu_outer_fixed_exact
  psp_outer_fixed_exact)

theorem no_omega_component_statedSp {m : ℕ} (hdet : OmegaEvenTypeDetAt m) {s : StatedLieTag}
    (hs : s = .POmegaPlus ∨ s = .POmegaMinus) {X : Type} [Group X] [Finite X] {k : Type}
    [Field k] [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r)
    (Φ : X ≃* StatedSp r k) {D : Subgroup X} (hD : IsComponent D) {f : ℕ}
    (hDm : LieModel (D ⧸ center D) s m 2 f) : False := by
  have hg : 1 ≤ g := by
    by_contra h0
    have hk1 : Nat.card k = 1 := by rw [hk, show g = 0 by omega, pow_zero]
    exact absurd hk1 (ne_of_gt Finite.one_lt_card)
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hk
  have hcardX : Nat.card X = Nat.card k ^ (r ^ 2) *
      ∏ j ∈ Finset.Icc 1 r, (Nat.card k ^ (2 * j) - 1) := by
    rw [Nat.card_congr Φ.toEquiv]
    exact LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp r
  have hdvdX : 2 ^ 12 ∣ Nat.card X :=
    ((two_pow_twelve_dvd_card_of_lieModel_POmega hs hDm).trans
      (card_quotient_dvd_card (center D))).trans (Subgroup.card_subgroup_dvd_card D)
  have hsmall : ¬ (g = 1 ∧ r ≤ 2) := by
    rintro ⟨rfl, hr2⟩
    rw [hcardX, hk, pow_one] at hdvdX
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · exact absurd (hdvdX.trans (dvd_of_eq (by decide) : _ ∣ 6)) (by decide)
    · exact absurd (hdvdX.trans (dvd_of_eq (by decide) : _ ∣ 720)) (by decide)
  obtain ⟨t, r', hX, hadm, hmX, ht⟩ : ∃ (t : StatedLieTag) (r' : ℕ),
      IsSimpleGroup X ∧ StatedLieAdmissible t r' 2 g ∧ LieModel X t r' 2 g ∧
        (t = .PSL ∨ t = .PSp) := by
    rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | hr2
    · have hg2 : 2 ≤ g := by omega
      obtain ⟨e₂⟩ := RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := k)
      have h4 : 4 ≤ 2 ^ g :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hadm : StatedLieAdmissible .PSL 2 2 g := ⟨Nat.prime_two, hg, le_rfl,
        fun h => by rw [Prod.mk.injEq] at h; omega,
        fun h => by rw [Prod.mk.injEq] at h; omega⟩
      have hstated : StatedClassicalModel X .PSL 2 2 g :=
        ⟨hadm, k, inferInstance, inferInstance, hk,
          ⟨(Φ.trans (ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k).symm).trans
            e₂⟩⟩
      exact ⟨.PSL, 2, (LieType.Simplicity.fam_PSL_simplicity X 2 2 g hstated).2, hadm,
        Or.inl ⟨by decide, hstated⟩, Or.inl rfl⟩
    · have hcond : (Infinite k ∨ 4 ≤ Nat.card k) ∨ (Nat.card k = 3 ∧ 2 ≤ r) ∨
          (Nat.card k = 2 ∧ 3 ≤ r) := by
        rcases (by omega : g = 1 ∨ 2 ≤ g) with rfl | hg2
        · exact Or.inr (Or.inr ⟨by rw [hk, pow_one], by omega⟩)
        · refine Or.inl (Or.inr ?_)
          rw [hk]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hS := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r (by omega) hcond
      obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
        SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
          (X := StatedSp r k) hk (by omega) ⟨MulEquiv.refl _⟩
      have hadm : StatedLieAdmissible .PSp r 2 g := ⟨Nat.prime_two, hg, hr2, fun h => by
        rw [Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        exact hsmall ⟨Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm), le_rfl⟩⟩
      exact ⟨.PSp, r, (Φ.trans eProj.symm).isSimpleGroup, hadm,
        Or.inl ⟨by decide, hadm, k, inferInstance, inferInstance, hk, ⟨Φ.trans eProj.symm⟩⟩,
        Or.inr rfl⟩
  have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
  let eD : D ≃* X := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
  have hDs : IsSimpleGroup D := eD.isSimpleGroup
  obtain ⟨htt, -, -⟩ := omegaTypeDet_of_simple hdet hD.1 hDs hs hDm hadm
    (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hmX)
  rcases ht with rfl | rfl <;> rcases hs with rfl | rfl <;> exact absurd htt (by decide)

theorem false_of_spFixedOrNoPComponent_omega {m : ℕ} (hdet : OmegaEvenTypeDetAt m)
    {s : StatedLieTag} (hs : s = .POmegaPlus ∨ s = .POmegaMinus) {X : Type} [Group X]
    [Finite X] {g : ℕ} (h : SpFixedOrNoPComponent X g) {D : Subgroup X} (hD : IsComponent D)
    {f : ℕ} (hDm : LieModel (D ⧸ center D) s m 2 f) : False := by
  rcases h with ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · exact no_omega_component_statedSp hdet hs hk hr Φ hD hDm
  · exact h D (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD)

theorem catOmegaEvenOuterFamilyAt_PSL {m : ℕ} (hdet : OmegaEvenTypeDetAt m) :
    CatOmegaEvenOuterFamilyAt .PSL m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout t f D ht hD hDm _
  have hDp : IsPComponent 2 D := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  rcases UnitaryPilot.psl_outer_fixed_even hadm hmS σ hσ hout with
    h | ⟨-, h⟩ | ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · obtain ⟨hadm', hmD, -⟩ := h D hDp
    obtain ⟨htt, -, -⟩ := omegaTypeDet_of_simple hdet hD.1
      (LinearPilot.isSimpleGroup_of_lieModel_PSL hmD) ht hDm hadm' hmD
    rcases ht with rfl | rfl <;> exact absurd htt (by decide)
  · obtain ⟨hadm', hmD⟩ := h D hDp
    obtain ⟨htt, -, -⟩ := omegaTypeDet_of_simple hdet hD.1
      (LinearPilot.isSimpleGroup_of_lieModel_PSU hmD) ht hDm hadm' hmD
    rcases ht with rfl | rfl <;> exact absurd htt (by decide)
  · exact (no_omega_component_statedSp hdet ht hk hr Φ hD hDm).elim
  · exact (h D hDp).elim

theorem catOmegaEvenOuterFamilyAt_PSU {m : ℕ} (hdet : OmegaEvenTypeDetAt m) :
    CatOmegaEvenOuterFamilyAt .PSU m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout t f D ht hD hDm _
  exact (false_of_spFixedOrNoPComponent_omega hdet ht
    (psu_outer_fixed_exact hadm hmS σ hσ hout) hD hDm).elim

theorem catOmegaEvenOuterFamilyAt_PSp {m : ℕ}
    (hdet : OmegaEvenTypeDetAt m) : CatOmegaEvenOuterFamilyAt .PSp m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout t f D ht hD hDm _
  rcases psp_outer_fixed_exact hadm hmS σ hσ hout with h | ⟨hS, hadmB, hLie⟩
  · exact (false_of_spFixedOrNoPComponent_omega hdet ht h hD hDm).elim
  · have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
    let eD : D ≃* fixedSubgroup σ := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
    have hDs : IsSimpleGroup D := eD.isSimpleGroup
    obtain ⟨htt, -, -⟩ := omegaTypeDet_of_simple hdet hD.1 hDs ht hDm hadmB
      (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hLie)
    rcases ht with rfl | rfl <;> exact absurd htt (by decide)

end CFSG.SeitzReduction.OmegaPilot
