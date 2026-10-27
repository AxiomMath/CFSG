module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatL3Ord
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34REvenExcB
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFClass
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (slmEvenTypeDetAt SpFixedOrNoPComponent
  false_of_spFixedOrNoPComponent psl_outer_fixed_exact psu_outer_fixed_exact psp_outer_fixed_exact
  omega_family_fixed_exact)

theorem lieModel_two_mul_of_classical_outer
    {S : Type} [Group S] [Finite S] {τ : StatedLieTag} {m f : ℕ}
    (hτ : τ ∈ Blueprint.classicalTags) (hadm : StatedLieAdmissible τ m 2 f)
    (hm : LieModel S τ m 2 f) {σ : MulAut S} (hσ2 : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {P : Subgroup (fixedSubgroup σ)}
    (hP : IsPComponent 2 P) [IsSimpleGroup P] {n : ℕ} (hn : 1 ≤ n)
    (hL : LieModel P .PSL 3 2 n) : LieModel S .PSL 3 2 (2 * n) := by
  have hdet := slmEvenTypeDetAt (m := 3) le_rfl
  obtain ⟨hD, hDm⟩ := isComponent_and_lieModel_of_simple_psl_three hP hn hL
  have hsp : ∀ {g : ℕ}, SpFixedOrNoPComponent (fixedSubgroup σ) g → False :=
    fun h => false_of_spFixedOrNoPComponent hdet h hD le_rfl hDm
  simp only [Blueprint.classicalTags, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases psl_outer_fixed_exact hadm hm σ hσ2 hout with h | h | h | h
    · obtain ⟨hadm', hm', h2⟩ := h P hP
      obtain ⟨-, rfl, h4⟩ := hdet _ n _ _ _ hL hadm' hm'
      obtain rfl : f = 2 * n := by omega
      exact hm
    · obtain ⟨hadm', hm'⟩ := h P hP
      exact absurd (hdet _ n _ _ _ hL hadm' hm').1 (by decide)
    · exact (hsp (Or.inl h)).elim
    · exact absurd hP (h P)
  · exact (hsp (psu_outer_fixed_exact hadm hm σ hσ2 hout)).elim
  · rcases psp_outer_fixed_exact hadm hm σ hσ2 hout with h | ⟨hs, hadmB, hmB⟩
    · exact (hsp h).elim
    · have htop := L34PF.eq_top_of_isPComponent_of_simple hP
      have hLF : LieModel (fixedSubgroup σ) .PSL 3 2 n :=
        LieType.CurtisTits.lieModel_of_mulEquiv
          ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) hL
      exact absurd (hdet _ n _ _ _ hLF hadmB hmB).1 (by decide)
  · exact absurd rfl hadm.2.2.2
  · rcases omega_family_fixed_exact (Or.inl rfl) hadm hm σ hσ2 hout with h | h
    · exact (hsp h).elim
    · obtain ⟨t, n', f', ht, hadm', hmP⟩ := h P hP
      have h1 := (hdet _ n _ _ _ hL hadm' hmP).1
      rcases ht with rfl | rfl <;> exact absurd h1 (by decide)
  · rcases omega_family_fixed_exact (Or.inr rfl) hadm hm σ hσ2 hout with h | h
    · exact (hsp h).elim
    · obtain ⟨t, n', f', ht, hadm', hmP⟩ := h P hP
      have h1 := (hdet _ n _ _ _ hL hadm' hmP).1
      rcases ht with rfl | rfl <;> exact absurd h1 (by decide)

section Nonclassical

open CFSG.SeitzReduction.F4Pilot

theorem false_of_evenLie_outer_nonclassical
    {S : Type} [Group S] [Finite S] {τ : StatedLieTag} {m f : ℕ}
    (hτ : τ ∉ Blueprint.classicalTags) (hadm : StatedLieAdmissible τ m 2 f)
    (hm : LieModel S τ m 2 f) {σ : MulAut S} (hσ2 : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {P : Subgroup (fixedSubgroup σ)}
    (hP : IsPComponent 2 P) {n : ℕ} (hn : 2 ≤ n)
    (hL : LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 n) : False := by
  have hX : ExcEvenType (P ⧸ Open.fusionZStar P) := by
    cases τ
    case G2 => exact evenOuterFamilyExcInput_G2 S m f hadm hm σ hσ2 hout P hP
    case F4 => exact evenOuterFamilyExcInput_F4 S m f hadm hm σ hσ2 hout P hP
    case E6 => exact evenOuterFamilyExcInput_E6 S m f hadm hm σ hσ2 hout P hP
    case E7 => exact evenOuterFamilyExcInput_E7_E8 (Or.inl rfl) S m f hadm hm σ hσ2 hout P hP
    case E8 => exact evenOuterFamilyExcInput_E7_E8 (Or.inr rfl) S m f hadm hm σ hσ2 hout P hP
    case twistedE6 => exact evenOuterFamilyExcInput_twistedE6 S m f hadm hm σ hσ2 hout P hP
    case trialityD4 => exact evenOuterFamilyExcInput_trialityD4 S m f hadm hm σ hσ2 hout P hP
    case twistedB2 => exact (L34R.false_of_outer_suzukiRee (Or.inl rfl) hadm hm hσ2 hout).elim
    case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
    case twistedF4 =>
      exact (L34R.false_of_outer_suzukiRee (Or.inr (Or.inl rfl)) hadm hm hσ2 hout).elim
    case Tits => exact (L34R.false_of_outer_suzukiRee (Or.inr (Or.inr rfl)) hadm hm hσ2 hout).elim
    all_goals exact absurd (by decide) hτ
  rcases hX with ⟨τ', e', hτ', hadm', hm'⟩ | hU
  · obtain ⟨rfl, -, -⟩ := slmEvenTypeDetAt (m := 3) le_rfl _ n τ' 0 e' hL hadm' hm'
    exact hτ' (by decide)
  · have h1 := pow_dvd_card_of_lieModel_psl_three (by omega) hL
    rw [GH74.card_of_lieModel_PSU (by norm_num) (by norm_num) hU,
      show Open.ordTwistedA (3 - 1) (3 ^ 1) = 6048 by decide] at h1
    exact absurd ((Nat.pow_dvd_pow 2 (by omega : 6 ≤ 3 * n)).trans h1) (by decide)

end Nonclassical

theorem lieModel_two_mul_of_evenLie_outer
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (heven : EvenLieType S) {σ : MulAut S}
    {P : Subgroup S} (h : CatLeaf.ProperFixedComponent σ P)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {n : ℕ} (hn : 4 ≤ n) (hev : Even n)
    (hL : LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 n) : LieModel S .PSL 3 2 (2 * n) := by
  have hσ2 : orderOf σ = 2 :=
    orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
  obtain ⟨τ, m, f, hadm, hm⟩ := heven
  by_cases hτ : τ ∈ Blueprint.classicalTags
  · have eP := subgroupOfEquivOfLe h.2.1
    have hdP : 20160 ∣ Nat.card P := (dvd_card_of_lieModel_psl_three_even (by omega) hev hL).trans
      (Subgroup.card_quotient_dvd_card _)
    have hd : 20160 ∣ Nat.card ↥(P.subgroupOf (fixedSubgroup σ)) := by
      rw [Nat.card_congr eP.toEquiv]
      exact hdP
    have hs := L34PF.isSimpleGroup_of_classical_outer hτ hadm hm hσ2 hout h.2.2.1 hd
    have : IsSimpleGroup P := eP.symm.isSimpleGroup
    have hna' : ∃ a b : P, a * b ≠ b * a :=
      L34PF.nonabelian_of_simple_of_four_dvd ((show 4 ∣ 20160 by norm_num).trans hdP)
    have hZ := L34PF.fusionZStar_eq_bot_of_simple hna' ((show 2 ∣ 20160 by norm_num).trans hdP)
    have e₁ : P ⧸ Open.fusionZStar P ≃* P :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact lieModel_two_mul_of_classical_outer hτ hadm hm hσ2 hout h.2.2.1 (by omega)
      (LieType.CurtisTits.lieModel_of_mulEquiv (e₁.trans eP.symm) hL)
  · obtain ⟨eP⟩ :=
      GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1).symm
    exact (false_of_evenLie_outer_nonclassical hτ hadm hm hσ2 hout h.2.2.1 (by omega)
      (LieType.CurtisTits.lieModel_of_mulEquiv eP hL)).elim

end CFSG.ComponentClassification.GrSLit.L34Sec5S
