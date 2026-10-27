module

public import CFSG.GH74.Uniqueness.SU.KI1r3FamDefs
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddHigherLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddSymplectic
public import CFSG.LieType.Chevalley.CLSOddG2F4E8AllInvolutionFourGroup
public import CFSG.LieType.Chevalley.CLSOddTrialityAllInvolutionFourGroup
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup
public import CFSG.LieType.Ree.SuzukiReeOuterTwoPart

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace FamLieAux

theorem fourFix_of_fixedSubgroup {K : Type} [Group K] [Finite K]
    (h : ∀ α : MulAut K, α ^ 2 = 1 → ∃ V : Subgroup K, V ≤ fixedSubgroup α ∧
      CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4) : FourFix K := by
  intro α hα
  obtain ⟨V, hV, hVel, hVc⟩ := h α hα
  exact Or.inl ⟨V, fun v hv => hV hv,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).1 hVel, hVc⟩

theorem statedClassical_of_lieModel {K : Type} [Group K] {t : StatedLieTag} {n p f : ℕ}
    (hn : n ≠ 0) (h : LieModel K t n p f) : StatedClassicalModel K t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem chevalley_of_lieModel_g2 {K : Type} [Group K] {p f : ℕ} (h : LieModel K .G2 0 p f) :
    ChevalleyExceptionalModel K .G2 p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by decide)

theorem chevalley_of_lieModel_trialityD4 {K : Type} [Group K] {p f : ℕ}
    (h : LieModel K .trialityD4 0 p f) : ChevalleyExceptionalModel K .trialityD4 p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by decide)

theorem ree_of_lieModel {K : Type} [Group K] {f : ℕ} (h : LieModel K .twistedG2 0 3 f) :
    ReeTitsModel K .twistedG2 3 f :=
  (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2

theorem alternatingGroup_nonabelian {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hc : IsMulCommutative (alternatingGroup (Fin n)) := ⟨⟨fun a b => hcon a b⟩⟩
  have h3 := alternatingGroup.isMulCommutative_iff_card_le_three.1 hc
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  omega

end FamLieAux

open FamLieAux
open CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear

theorem famAlt : FamAlt := by
  intro n hn7 _ α hα
  by_cases hα1 : α = 1
  · subst hα1
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    obtain ⟨V, -, hVel, hVc⟩ := four_group_fixed_of_inner
      (alternatingGroup_nonabelian (n := n) (by omega)) 1 (by rw [map_one, one_pow])
    exact Or.inl ⟨V, fun v _ => by rw [MulAut.one_apply], hVel, hVc⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨⟨V, hV, hVel, hVc⟩, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.alternating_at_least_seven_involution_fixed_four_group
        hn7 α (orderOf_eq_prime hα hα1)
    exact Or.inl ⟨V, fun v hv => hV hv,
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).1 hVel, hVc⟩

theorem famLie_psl3 : FamLie .PSL 3 := by
  intro K _ _ _ _ p f _ hp2 h
  exact fourFix_of_fixedSubgroup fun α hα =>
    odd_higher_linear_all_involution_fixed_four_group
      K hp2 (by norm_num) (statedClassical_of_lieModel (by norm_num) h) α hα

theorem famLie_psl4 : FamLie .PSL 4 := by
  intro K _ _ _ _ p f _ hp2 h
  exact fourFix_of_fixedSubgroup fun α hα =>
    odd_higher_linear_all_involution_fixed_four_group
      K hp2 (by norm_num) (statedClassical_of_lieModel (by norm_num) h) α hα

theorem famLie_psl5 : FamLie .PSL 5 := by
  intro K _ _ _ _ p f _ hp2 h
  exact fourFix_of_fixedSubgroup fun α hα =>
    odd_higher_linear_all_involution_fixed_four_group
      K hp2 (by norm_num) (statedClassical_of_lieModel (by norm_num) h) α hα

theorem famLie_psu3 : FamLie .PSU 3 := by
  intro K _ _ _ _ p f _ hp2 h
  exact fourFix_of_fixedSubgroup fun α hα =>
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.odd_unitary_all_involution_fixed_four_group
      K hp2 (statedClassical_of_lieModel (by norm_num) h) α hα

theorem famLie_psu4 : FamLie .PSU 4 := by
  intro K _ _ _ _ p f _ hp2 h
  exact fourFix_of_fixedSubgroup fun α hα =>
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.odd_unitary_all_involution_fixed_four_group
      K hp2 (statedClassical_of_lieModel (by norm_num) h) α hα

theorem famLie_psu5 : FamLie .PSU 5 := by
  intro K _ _ _ _ p f _ hp2 h
  exact fourFix_of_fixedSubgroup fun α hα =>
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.odd_unitary_all_involution_fixed_four_group
      K hp2 (statedClassical_of_lieModel (by norm_num) h) α hα

theorem famLie_psp2 : FamLie .PSp 2 := by
  intro K _ _ _ _ p f _ hp2 h
  exact fourFix_of_fixedSubgroup fun α hα =>
    CFSG.LocalAnalysis.ComponentInitial.OddSymplectic.odd_symplectic_all_involution_fixed_four_group
      K hp2 (statedClassical_of_lieModel (by norm_num) h) α hα

theorem famLie_g2 :
    FamLie .G2 0 := by
  intro K _ _ hsimple hnab p f hp hp2 h
  have := hsimple
  have hS := chevalley_of_lieModel_g2 h
  exact fourFix_of_fixedSubgroup fun α hα =>
    CFSG.LieType.Chevalley.odd_G2_F4_E8_all_involution_fixed_four_group K hnab .G2 (Or.inl rfl)
      hp hp2 hS.1.2.1 hS α hα

theorem famLie_3d4 :
    FamLie .trialityD4 0 := by
  intro K _ _ hsimple hnab p f hp hp2 h
  have := hsimple
  have hS := chevalley_of_lieModel_trialityD4 h
  exact fourFix_of_fixedSubgroup fun α hα =>
    CFSG.LieType.Chevalley.odd_triality_all_involution_fixed_four_group K hnab hp hp2 hS.1.2.1 hS
      α hα

theorem famRee :
    FamRee := by
  intro K _ _ hsimple hnab f h
  have := hsimple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine FourFix.of_inner hnab fun α hα => ?_
  have hout := (CFSG.LieType.Ree.SuzukiReeOuterTwoPart.small_Ree_case (ree_of_lieModel h)).1
  have : Finite (MulAut K) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (Outer K) := Nat.card_pos
  have hodd : ¬ 2 ∣ Nat.card (Outer K) := by
    intro h2
    have h3 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos.ne' h2
    exact (Nat.ne_of_gt (Nat.one_lt_two_pow h3.ne')) hout
  have hx2 : (QuotientGroup.mk α : Outer K) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have hx1 : (QuotientGroup.mk α : Outer K) = 1 := by
    by_contra hne
    have hord := orderOf_eq_prime hx2 hne
    have hdvd := orderOf_dvd_natCard (QuotientGroup.mk α : Outer K)
    rw [hord] at hdvd
    exact hodd hdvd
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff α).1 hx1
  exact ⟨g, hg.symm⟩

end CFSG.GH74.Uniqueness.SU.K.R3
