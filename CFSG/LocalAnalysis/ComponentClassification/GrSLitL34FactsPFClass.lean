module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFBase
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterOmega

public section

namespace CFSG.ComponentClassification.GrSLit.L34PF

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot

theorem isSimpleGroup_of_statedSp_even {X : Type} [Group X] [Finite X] {k : Type} [Field k]
    [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hg : 1 ≤ g) (hr : 1 ≤ r)
    (hsmall : ¬ (g = 1 ∧ r ≤ 2)) (Φ : X ≃* StatedSp r k) : IsSimpleGroup X := by
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hk
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
    exact (LieType.Simplicity.fam_PSL_simplicity X 2 2 g hstated).2
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
    exact (Φ.trans eProj.symm).isSimpleGroup

theorem isSimpleGroup_of_statedSp {X : Type} [Group X] [Finite X] {k : Type} [Field k]
    [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r) (Φ : X ≃* StatedSp r k)
    {P : Subgroup X} (hP : IsPComponent 2 P) (hd : 20160 ∣ Nat.card P) : IsSimpleGroup P := by
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
  have hdX : 20160 ∣ Nat.card X := hd.trans (Subgroup.card_subgroup_dvd_card P)
  have hsmall : ¬ (g = 1 ∧ r ≤ 2) := by
    rintro ⟨rfl, hr2⟩
    rw [hcardX, hk, pow_one] at hdX
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · exact absurd hdX (by decide)
    · exact absurd hdX (by decide)
  have hX := isSimpleGroup_of_statedSp_even hk hg hr hsmall Φ
  have htop := eq_top_of_isPComponent_of_simple hP
  exact ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).isSimpleGroup

theorem isSimpleGroup_of_spFixedOrNoPComponent {X : Type} [Group X] [Finite X] {g : ℕ}
    (h : SpFixedOrNoPComponent X g) {P : Subgroup X} (hP : IsPComponent 2 P)
    (hd : 20160 ∣ Nat.card P) : IsSimpleGroup P := by
  rcases h with ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · exact isSimpleGroup_of_statedSp hk hr Φ hP hd
  · exact absurd hP (h P)

theorem isSimpleGroup_of_classical_outer {S : Type} [Group S]
    [Finite S] {τ : StatedLieTag} {n f : ℕ} (hτ : τ ∈ Blueprint.classicalTags)
    (hadm : StatedLieAdmissible τ n 2 f) (hm : LieModel S τ n 2 f) {σ : MulAut S}
    (hσ2 : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {P : Subgroup (fixedSubgroup σ)}
    (hP : IsPComponent 2 P) (hd : 20160 ∣ Nat.card P) : IsSimpleGroup P := by
  simp only [Blueprint.classicalTags, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases psl_outer_fixed_exact hadm hm σ hσ2 hout with h | h | h | h
    · exact isSimpleGroup_of_lieModel_PSL (h P hP).2.1
    · exact isSimpleGroup_of_lieModel_PSU (h P hP).2
    · exact isSimpleGroup_of_spFixedOrNoPComponent (Or.inl h) hP hd
    · exact absurd hP (h P)
  · exact isSimpleGroup_of_spFixedOrNoPComponent (psu_outer_fixed_exact hadm hm σ hσ2 hout) hP hd
  · rcases psp_outer_fixed_exact hadm hm σ hσ2 hout with h | ⟨hs, -, -⟩
    · exact isSimpleGroup_of_spFixedOrNoPComponent h hP hd
    · have htop := eq_top_of_isPComponent_of_simple hP
      exact ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).isSimpleGroup
  · exact absurd rfl hadm.2.2.2
  · rcases omega_family_fixed_exact (Or.inl rfl) hadm hm σ hσ2 hout with h | h
    · exact isSimpleGroup_of_spFixedOrNoPComponent h hP hd
    · obtain ⟨t, n', f', ht, -, hmP⟩ := h P hP
      exact isSimpleGroup_of_lieModel_POmega ht hmP
  · rcases omega_family_fixed_exact (Or.inr rfl) hadm hm σ hσ2 hout with h | h
    · exact isSimpleGroup_of_spFixedOrNoPComponent h hP hd
    · obtain ⟨t, n', f', ht, -, hmP⟩ := h P hP
      exact isSimpleGroup_of_lieModel_POmega ht hmP

end CFSG.ComponentClassification.GrSLit.L34PF
