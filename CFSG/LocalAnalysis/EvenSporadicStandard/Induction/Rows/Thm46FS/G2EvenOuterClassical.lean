module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.G2EvenOuterBasic
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.G2EvenOuterTypeDet

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.RankOne (SpFixedRankOrNoPComponent)
open CFSG.ComponentClassification.SymmetricLocal
  (small_standard_source_even_simple_symplectic_parameters_stated)


theorem false_of_isPComponent_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {m g : ℕ} (ht : t ≠ .G2) (hm : LieModel X t m 2 g) {P : Subgroup X}
    (hP : IsPComponent 2 P) {n : ℕ} (hG : LieModel (P ⧸ Open.fusionZStar P) .G2 0 2 n) :
    False := by
  obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv (MulEquiv.refl X) hP
  exact false_of_lieModel_G2_of_ne (LieType.CurtisTits.lieModel_of_mulEquiv E hG) ht hm

theorem false_of_isPComponent_classical {X : Type} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsPComponent 2 P) {t : StatedLieTag} {m g : ℕ} (ht : t ∈ classicalTags)
    (hm : LieModel P t m 2 g) {n : ℕ} (hG : LieModel (P ⧸ Open.fusionZStar P) .G2 0 2 n) :
    False := by
  have : IsSimpleGroup P := LieModel.isSimpleGroup_of_mem_classicalTags ht hm
  obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP (MulEquiv.refl P)
  refine false_of_lieModel_G2_of_ne (LieType.CurtisTits.lieModel_of_mulEquiv E hG) ?_ hm
  rintro rfl
  exact absurd ht (by decide)

theorem false_of_isPComponent_statedSp {X : Type} [Group X] [Finite X] {k : Type} [Field k]
    [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r) (Φ : X ≃* StatedSp r k)
    {P : Subgroup X} (hP : IsPComponent 2 P) {n : ℕ}
    (hG : LieModel (P ⧸ Open.fusionZStar P) .G2 0 2 n) : False := by
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
  have h212 : 2 ^ 12 ∣ Nat.card X :=
    (two_pow_twelve_dvd_card_of_lieModel_G2 hG).trans
      ((Subgroup.card_quotient_dvd_card (Open.fusionZStar P)).trans
        (Subgroup.card_subgroup_dvd_card P))
  have hsmall : ¬ (g = 1 ∧ r ≤ 2) := by
    rintro ⟨rfl, hr2⟩
    rw [hcardX, hk, pow_one] at h212
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · exact absurd h212 (by decide)
    · exact absurd h212 (by decide)
  obtain ⟨t, r', hX, hm, ht⟩ : ∃ (t : StatedLieTag) (r' : ℕ),
      IsSimpleGroup X ∧ LieModel X t r' 2 g ∧ t ≠ .G2 := by
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
      exact ⟨.PSL, 2, (LieType.Simplicity.fam_PSL_simplicity X 2 2 g hstated).2,
        Or.inl ⟨by decide, hstated⟩, by decide⟩
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
      exact ⟨.PSp, r, (Φ.trans eProj.symm).isSimpleGroup,
        Or.inl ⟨by decide, hadm, k, inferInstance, inferInstance, hk, ⟨Φ.trans eProj.symm⟩⟩,
        by decide⟩
  haveI := hX
  exact false_of_isPComponent_of_simple ht hm hP hG

theorem false_of_spFixedRankOrNoPComponent {X : Type} [Group X] [Finite X] {g : ℕ}
    {R : ℕ → Prop} (h : SpFixedRankOrNoPComponent X g R) {P : Subgroup X}
    (hP : IsPComponent 2 P) {n : ℕ} (hG : LieModel (P ⧸ Open.fusionZStar P) .G2 0 2 n) :
    False := by
  rcases h with ⟨k, _, _, r, hk, hr, -, ⟨Φ⟩⟩ | h
  · exact false_of_isPComponent_statedSp hk hr Φ hP hG
  · exact h P hP

theorem g2EvenOuterFamily_PSL : G2EvenOuterFamily .PSL := by
  intro K _ _ m f hadm hmK α hα hout P hP n hG
  rcases SeitzReduction.RankOne.psl_outer_fixed_rank hadm hmK α hα hout with h | h | h
  · obtain ⟨-, hm', -⟩ := h P hP
    exact (false_of_isPComponent_classical hP (by decide) hm' hG).elim
  · obtain ⟨-, hm'⟩ := h P hP
    exact (false_of_isPComponent_classical hP (by decide) hm' hG).elim
  · exact (false_of_spFixedRankOrNoPComponent h hP hG).elim

theorem g2EvenOuterFamily_PSU : G2EvenOuterFamily .PSU := by
  intro K _ _ m f hadm hmK α hα hout P hP n hG
  exact (false_of_spFixedRankOrNoPComponent
    (SeitzReduction.RankOne.psu_outer_fixed_rank hadm hmK α hα hout) hP hG).elim

theorem g2EvenOuterFamily_PSp : G2EvenOuterFamily .PSp := by
  intro K _ _ m f hadm hmK α hα hout P hP n hG
  rcases SeitzReduction.SymplecticPilot.psp_outer_fixed_sp2m hadm hmK α hα hout with
    ⟨k, _, _, hk, -, ⟨Φ⟩⟩ | ⟨hS, -, hLie⟩
  · exact (false_of_isPComponent_statedSp hk (by have := hadm.2.2.1; omega) Φ hP hG).elim
  · haveI := hS
    exact (false_of_isPComponent_of_simple (by decide) hLie hP hG).elim

theorem g2EvenOuterFamily_POmega {τ : StatedLieTag} (hτ : τ = .POmegaPlus ∨ τ = .POmegaMinus) :
    G2EvenOuterFamily τ := by
  intro K _ _ m f hadm hmK α hα hout P hP n hG
  rcases SeitzReduction.RankOne.omega_family_fixed_rank hτ hadm hmK α hα hout with h | h
  · exact (false_of_spFixedRankOrNoPComponent h hP hG).elim
  · obtain ⟨t', m', f', ht', -, hm'⟩ := h P hP
    exact (false_of_isPComponent_classical hP
      (by rcases ht' with rfl | rfl <;> decide) hm' hG).elim

theorem g2EvenOuterFamily_POmegaPlus : G2EvenOuterFamily .POmegaPlus :=
  g2EvenOuterFamily_POmega (Or.inl rfl)

theorem g2EvenOuterFamily_POmegaMinus : G2EvenOuterFamily .POmegaMinus :=
  g2EvenOuterFamily_POmega (Or.inr rfl)

end CFSG.EvenSporadicStandard.Induction
