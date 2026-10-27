module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatEvenOuter
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalOmega
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalPSL
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalPSU
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalPSp

public section

namespace CFSG.SeitzReduction.E8Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.SymmetricLocal
  (small_standard_source_even_simple_symplectic_parameters_stated)


theorem two_pow_dvd_card_of_lieModel_E7_two {D : Type} [Group D] {n f : ℕ}
    (h : LieModel D .E7 n 2 f) : 2 ^ 63 ∣ Nat.card D := by
  obtain ⟨hf, A, -, -, hD⟩ := card_of_lieModel_E7_two_bounds h
  rw [hD]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (dvd_pow_self 2 (by omega)) 63) _

theorem false_of_isComponent_statedSp_E7 {X : Type} [Group X] [Finite X]
    {k : Type} [Field k] [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r)
    (Φ : X ≃* StatedSp r k) {D : Subgroup X} (hD : IsComponent D) {f : ℕ}
    (hD7 : LieModel D .E7 0 2 f) : False := by
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
  have h63 : 2 ^ 63 ∣ Nat.card X :=
    (two_pow_dvd_card_of_lieModel_E7_two hD7).trans (Subgroup.card_subgroup_dvd_card D)
  have hsmall : ¬ (g = 1 ∧ r ≤ 2) := by
    rintro ⟨rfl, hr2⟩
    rw [hcardX, hk, pow_one] at h63
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · exact absurd h63 (by decide)
    · exact absurd h63 (by decide)
  obtain ⟨t, r', hr', hX, hadm, hm⟩ : ∃ (t : StatedLieTag) (r' : ℕ), 1 ≤ r' ∧
      IsSimpleGroup X ∧ StatedLieAdmissible t r' 2 g ∧ LieModel X t r' 2 g := by
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
      exact ⟨.PSL, 2, by norm_num, (LieType.Simplicity.fam_PSL_simplicity X 2 2 g hstated).2, hadm,
        Or.inl ⟨by decide, hstated⟩⟩
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
        small_standard_source_even_simple_symplectic_parameters_stated (X := StatedSp r k) hk
          (by omega) ⟨MulEquiv.refl _⟩
      have hadm : StatedLieAdmissible .PSp r 2 g := ⟨Nat.prime_two, hg, hr2, fun h => by
        rw [Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        exact hsmall ⟨Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm), le_rfl⟩⟩
      exact ⟨.PSp, r, by omega, (Φ.trans eProj.symm).isSimpleGroup, hadm,
        Or.inl ⟨by decide, hadm, k, inferInstance, inferInstance, hk, ⟨Φ.trans eProj.symm⟩⟩⟩
  have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
  let eD : D ≃* X := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
  exact not_lieModel_classicalOrSuzuki_of_card_eq_E7 hD7
    (F4Pilot.classicalOrSuzukiTag_of_admissible hadm hr') hm (Nat.card_congr eD.toEquiv).symm

theorem false_of_notSp6Components_E7 {X : Type} [Group X] [Finite X]
    (h : F4Pilot.NotSp6Components X) {D : Subgroup X} (hD : IsComponent D) {f : ℕ}
    (hD7 : LieModel D .E7 0 2 f) : False := by
  obtain ⟨t, n, f', hT, -, hm, -⟩ :=
    h D (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD)
  exact not_lieModel_classicalOrSuzuki_of_card_eq_E7 hD7 hT hm rfl

theorem false_of_spFixedOrNotSp6_E7 {X : Type} [Group X] [Finite X] {R : ℕ → ℕ → Prop}
    (h : F4Pilot.SpFixedOrNotSp6 X R) {D : Subgroup X} (hD : IsComponent D) {f : ℕ}
    (hD7 : LieModel D .E7 0 2 f) : False := by
  rcases h with ⟨k, _, _, r, g, hk, hr, -, ⟨Φ⟩⟩ | h
  · exact false_of_isComponent_statedSp_E7 hk hr Φ hD hD7
  · exact false_of_notSp6Components_E7 h hD hD7

theorem catE7EvenOuterFamily_PSL : CatE7EvenOuterFamily .PSL :=
  catE7EvenOuterFamily_of_forall_false fun _ _ _ _ _ hadm hm σ hσ hout _ _ hD hD7 =>
    false_of_spFixedOrNotSp6_E7 (F4Pilot.psl_outer_fixed hadm hm σ hσ hout) hD hD7

theorem catE7EvenOuterFamily_PSU : CatE7EvenOuterFamily .PSU :=
  catE7EvenOuterFamily_of_forall_false fun _ _ _ _ _ hadm hm σ hσ hout _ _ hD hD7 =>
    false_of_spFixedOrNotSp6_E7 (F4Pilot.psu_outer_fixed hadm hm σ hσ hout) hD hD7

theorem catE7EvenOuterFamily_PSp : CatE7EvenOuterFamily .PSp :=
  catE7EvenOuterFamily_of_forall_false fun _ _ _ _ _ hadm hm σ hσ hout _ _ hD hD7 =>
    false_of_spFixedOrNotSp6_E7 (F4Pilot.psp_outer_fixed hadm hm σ hσ hout) hD hD7

theorem catE7EvenOuterFamily_POmegaPlus : CatE7EvenOuterFamily .POmegaPlus :=
  catE7EvenOuterFamily_of_forall_false fun _ _ _ _ _ hadm hm σ hσ hout _ _ hD hD7 =>
    false_of_spFixedOrNotSp6_E7 (F4Pilot.omega_family_fixed (Or.inl rfl) hadm hm σ hσ hout) hD
      hD7

theorem catE7EvenOuterFamily_POmegaMinus : CatE7EvenOuterFamily .POmegaMinus :=
  catE7EvenOuterFamily_of_forall_false fun _ _ _ _ _ hadm hm σ hσ hout _ _ hD hD7 =>
    false_of_spFixedOrNotSp6_E7 (F4Pilot.omega_family_fixed (Or.inr rfl) hadm hm σ hσ hout) hD
      hD7

end CFSG.SeitzReduction.E8Pilot
