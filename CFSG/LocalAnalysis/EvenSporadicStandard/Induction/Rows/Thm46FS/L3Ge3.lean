module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.CatFS46
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.Arith
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatL3Out
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatL3Spor
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GrSLit.L34Sec5S CFSG.ComponentClassification.GrSLit.L34PF
open CFSG.SeitzReduction.LinearPilot


theorem isSimpleGroup_of_statedSp_gt {X : Type} [Group X] [Finite X] {k : Type} [Field k]
    [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r) (Φ : X ≃* StatedSp r k)
    {P : Subgroup X} (hP : IsPComponent 2 P) (hd : 720 < Nat.card P) : IsSimpleGroup P := by
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
  have hdX : 720 < Nat.card X := lt_of_lt_of_le hd (Subgroup.card_le_card_group P)
  have hsmall : ¬ (g = 1 ∧ r ≤ 2) := by
    rintro ⟨rfl, hr2⟩
    rw [hcardX, hk, pow_one] at hdX
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · exact absurd hdX (by decide)
    · exact absurd hdX (by decide)
  have hX := isSimpleGroup_of_statedSp_even hk hg hr hsmall Φ
  have htop := eq_top_of_isPComponent_of_simple hP
  exact ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).isSimpleGroup

theorem isSimpleGroup_of_spFixedOrNoPComponent_gt {X : Type} [Group X] [Finite X] {g : ℕ}
    (h : SpFixedOrNoPComponent X g) {P : Subgroup X} (hP : IsPComponent 2 P)
    (hd : 720 < Nat.card P) : IsSimpleGroup P := by
  rcases h with ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · exact isSimpleGroup_of_statedSp_gt hk hr Φ hP hd
  · exact absurd hP (h P)

theorem isSimpleGroup_of_classical_outer_gt {S : Type} [Group S]
    [Finite S] {τ : StatedLieTag} {n f : ℕ} (hτ : τ ∈ Blueprint.classicalTags)
    (hadm : StatedLieAdmissible τ n 2 f) (hm : LieModel S τ n 2 f) {σ : MulAut S}
    (hσ2 : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {P : Subgroup (fixedSubgroup σ)}
    (hP : IsPComponent 2 P) (hd : 720 < Nat.card P) : IsSimpleGroup P := by
  simp only [Blueprint.classicalTags, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases psl_outer_fixed_exact hadm hm σ hσ2 hout with h | h | h | h
    · exact isSimpleGroup_of_lieModel_PSL (h P hP).2.1
    · exact isSimpleGroup_of_lieModel_PSU (h P hP).2
    · exact isSimpleGroup_of_spFixedOrNoPComponent_gt (Or.inl h) hP hd
    · exact absurd hP (h P)
  · exact isSimpleGroup_of_spFixedOrNoPComponent_gt (psu_outer_fixed_exact hadm hm σ hσ2 hout) hP hd
  · rcases psp_outer_fixed_exact hadm hm σ hσ2 hout with h | ⟨hs, -, -⟩
    · exact isSimpleGroup_of_spFixedOrNoPComponent_gt h hP hd
    · have htop := eq_top_of_isPComponent_of_simple hP
      exact ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).isSimpleGroup
  · exact absurd rfl hadm.2.2.2
  · rcases omega_family_fixed_exact (Or.inl rfl) hadm hm σ hσ2 hout with h | h
    · exact isSimpleGroup_of_spFixedOrNoPComponent_gt h hP hd
    · obtain ⟨t, n', f', ht, -, hmP⟩ := h P hP
      exact isSimpleGroup_of_lieModel_POmega ht hmP
  · rcases omega_family_fixed_exact (Or.inr rfl) hadm hm σ hσ2 hout with h | h
    · exact isSimpleGroup_of_spFixedOrNoPComponent_gt h hP hd
    · obtain ⟨t, n', f', ht, -, hmP⟩ := h P hP
      exact isSimpleGroup_of_lieModel_POmega ht hmP

theorem lieModel_two_mul_of_evenLie_outer_ge3
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (heven : EvenLieType S) {σ : MulAut S}
    {P : Subgroup S} (h : CatLeaf.ProperFixedComponent σ P)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {n : ℕ} (hn : 3 ≤ n)
    (hL : LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 n) : LieModel S .PSL 3 2 (2 * n) := by
  have hσ2 : orderOf σ = 2 :=
    orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
  obtain ⟨τ, m, f, hadm, hm⟩ := heven
  by_cases hτ : τ ∈ Blueprint.classicalTags
  · have eP := subgroupOfEquivOfLe h.2.1
    have hcQ : Nat.card (P ⧸ Open.fusionZStar P) = Open.ordA 2 (2 ^ n) :=
      card_of_lieModel_psl_three hL
    have hgt : 95040 < Nat.card (P ⧸ Open.fusionZStar P) := by
      rw [hcQ]
      exact ordA_two_pow_gt n hn
    have hdP : 720 < Nat.card P := by
      have h1 : Nat.card (P ⧸ Open.fusionZStar P) ≤ Nat.card P :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
      omega
    have hd : 720 < Nat.card ↥(P.subgroupOf (fixedSubgroup σ)) := by
      rw [Nat.card_congr eP.toEquiv]
      exact hdP
    have hs := isSimpleGroup_of_classical_outer_gt hτ hadm hm hσ2 hout h.2.2.1 hd
    have : IsSimpleGroup P := eP.symm.isSimpleGroup
    have h4 : 4 ∣ Nat.card P := by
      have := pow_dvd_card_of_lieModel_psl_three (by omega : 1 ≤ n) hL
      exact ((show (4 : ℕ) ∣ 2 ^ (3 * n) from
        Nat.pow_dvd_pow 2 (by omega : 2 ≤ 3 * n)).trans this).trans
        (Subgroup.card_quotient_dvd_card _)
    have hna' : ∃ a b : P, a * b ≠ b * a := nonabelian_of_simple_of_four_dvd h4
    have hZ := fusionZStar_eq_bot_of_simple hna' ((show 2 ∣ 4 by norm_num).trans h4)
    have e₁ : P ⧸ Open.fusionZStar P ≃* P :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact lieModel_two_mul_of_classical_outer hτ hadm hm hσ2 hout h.2.2.1 (by omega)
      (LieType.CurtisTits.lieModel_of_mulEquiv (e₁.trans eP.symm) hL)
  · obtain ⟨eP⟩ :=
      GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1).symm
    exact (false_of_evenLie_outer_nonclassical hτ hadm hm hσ2 hout h.2.2.1 (by omega)
      (LieType.CurtisTits.lieModel_of_mulEquiv eP hL)).elim

theorem l3FixedCatalogGe3_holds : L3FixedCatalogGe3 := by
  intro n hn S _ _ hs hna hcat σ hσ P hPF hP hPne hL
  have : IsSimpleGroup S := hs
  have h : CatLeaf.ProperFixedComponent σ P := ⟨hσ, hPF, hP, hPne⟩
  have hR : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → LieModel X .PSL 3 2 n →
      LieModel Y .PSL 3 2 n := fun _ _ _ _ e hX => LieType.CurtisTits.lieModel_of_mulEquiv e hX
  have hsmall : ∀ M : ℕ, ¬ 2 ^ 12 ∣ M → ¬ 16482816 ∣ M →
      ∀ (X : Type) [Group X] [Finite X], LieModel X .PSL 3 2 n → ¬ Nat.card X ∣ M := by
    intro M h12 h16 X _ _ hX hd
    by_cases h4 : 4 ≤ n
    · exact h12 (((Nat.pow_dvd_pow 2 (by omega : 12 ≤ 3 * n)).trans
        (pow_dvd_card_of_lieModel_psl_three (by omega) hX)).trans hd)
    · obtain rfl : n = 3 := by omega
      have hc : Nat.card X = 16482816 := by
        rw [card_of_lieModel_psl_three hX, ordA_two]
        norm_num
      rw [hc] at hd
      exact h16 hd
  have hRalt : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], 5 ≤ Fintype.card Ω →
      ¬ LieModel (alternatingGroup Ω) .PSL 3 2 n := by
    intro Ω _ _ hΩ hA
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have h1 := SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hA
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card] at h1
    rcases SeitzReduction.LinearPilot.ordA_two_pow_eq_factorial_div_two (n := 3 - 1)
      (by norm_num) (by omega) h1.symm with h2 | h2 <;> omega
  have hRodd : ∀ (X : Type) [Group X] (t : StatedLieTag) (n' p f : ℕ), p.Prime → p ≠ 2 →
      StatedLieAdmissible t n' p f → LieModel X t n' p f → ¬ LieModel X .PSL 3 2 n :=
    fun X _ t n' p f hp hp2 hadm hm hX => SeitzReduction.CrossChar.sLmNotOddLieInputAt
      (m := 3) (by norm_num) X n (fun h3 => by rw [Prod.mk.injEq] at h3; omega) hX
      ⟨t, n', p, f, hp, hp2, hadm, hm⟩
  have h360 := hsmall 360 (by decide) (by decide)
  have h504 := hsmall 504 (by decide) (by decide)
  have h20160 := hsmall 20160 (by decide) (by decide)
  have hHe := hsmall 4030387200 (by decide) (by decide)
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨k, hk, ⟨θ⟩⟩ | ho | he | hsp
  · exact (not_of_properFixedComponent_alternating (R := fun X _ => LieModel X .PSL 3 2 n) hR
      hRalt h360 hk θ h hL).elim
  · exact (not_of_properFixedComponent_oddLie (R := fun X _ => LieModel X .PSL 3 2 n)
      SeitzReduction.gls3OddLieAutComponentsInput CatLeafProof.lieOrderFormulasInput
      hR hRodd h504 hna ho h hL).elim
  · rcases CatLeaf.exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
    · exact (not_of_properFixedComponent_evenLie_inner (R := fun X _ => LieModel X .PSL 3 2 n)
        SeitzReduction.gls3OddLieAutComponentsInput CatLeafProof.lieOrderFormulasInput hR hRalt
        h360 hRodd h504 h20160 hHe hna he h ht hL).elim
    · exact lieModel_two_mul_of_evenLie_outer_ge3 he h hout hn hL
  · exact (false_of_properFixedComponent_sporadic_psl_three CatLeafProof.monsterInnerInput
      CatLeafProof.monsterLocalComponentsInput hna hsp h hn hL).elim

end CFSG.EvenSporadicStandard.Induction
