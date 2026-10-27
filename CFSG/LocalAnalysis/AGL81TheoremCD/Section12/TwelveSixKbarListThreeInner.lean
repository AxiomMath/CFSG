module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarListThreeTools
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33PartialRanks
import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddL3
import CFSG.RankThree.PartTwo.Sec4.Item49OddChar
import CFSG.RankThree.PartTwo.Sec4.Item49Small
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutTriD4
import CFSG.RankThree.PartTwo.Census.Carrier.TitsCert
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListThree

open CFSG.Open CFSG.Blueprint Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
  (pRank_three_eq_two_of_lieModel_PSL_three_three_one
    pRank_three_eq_two_of_lieModel_PSU_three_three_one
    pRank_three_eq_two_of_lieModel_trialityD4_two_one pRank_three_eq_two_of_isSpor_M11
    pRank_three_eq_two_of_isSpor_M12)

theorem false_of_psl_three_three {S : Type} [Group S] [Finite S] (hZ : center S = ⊥)
    (hS : StatedClassicalModel S .PSL 3 3 1) {V : Subgroup (MulAut S)} (hV : IsElemAbelian 3 V)
    (hc : Nat.card V = 27) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr := pRank_three_eq_two_of_lieModel_PSL_three_three_one (Or.inl ⟨by decide, hS⟩)
  obtain ⟨a⟩ := CFSG.RankThree.PartTwo.Sec14.Ronan148T.nonempty_projSL_of_statedClassicalModel hS
  have hout := CFSG.RankThree.PartTwo.Sec4.Item49OddChar.not_three_dvd_card_outer_of_mulEquiv a
    (CFSG.RankThree.PartTwo.Sec4.Item49Small.not_three_dvd_card_outer_projSL (n := 3) (e := 1)
      (by norm_num) le_rfl (by norm_num))
  exact false_of_le_inner hZ hr.le hV hc (le_inner_of_not_three_dvd hout hV)

theorem false_of_psu_three_three {S : Type} [Group S] [Finite S] (hZ : center S = ⊥)
    (hS : StatedClassicalModel S .PSU 3 3 1) {V : Subgroup (MulAut S)} (hV : IsElemAbelian 3 V)
    (hc : Nat.card V = 27) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr := pRank_three_eq_two_of_lieModel_PSU_three_three_one (Or.inl ⟨by decide, hS⟩)
  obtain ⟨a⟩ := CFSG.RankThree.PartTwo.Sec14.Ronan148T.nonempty_projSU_of_statedClassicalModel hS
  have hout := CFSG.RankThree.PartTwo.Sec4.Item49OddChar.not_three_dvd_card_outer_of_mulEquiv a
    (CFSG.RankThree.PartTwo.Sec4.Item49Small.not_three_dvd_card_outer_projSU (n := 3) (e := 1)
      (by norm_num) le_rfl (by norm_num))
  exact false_of_le_inner hZ hr.le hV hc (le_inner_of_not_three_dvd hout hV)

theorem false_of_trialityD4
    {S : Type} [Group S] [Finite S] (hZ : center S = ⊥) (hS : LieModel S .trialityD4 0 2 1)
    {V : Subgroup (MulAut S)} (hV : IsElemAbelian 3 V) (hc : Nat.card V = 27)
    (hVd : V ≤ commutator (MulAut S)) : False := by
  have hr := pRank_three_eq_two_of_lieModel_trialityD4_two_one hS
  refine false_of_le_inner hZ hr.le hV hc fun v hv => ?_
  have hvD : v ∈ innAutDerived S := (le_sup_right : commutator (MulAut S) ≤ _) (hVd hv)
  exact CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outtrid4_isInnerAut_of_mem_innAutDerived hS hvD

theorem false_of_tits
    {S : Type} [Group S] [Finite S] (hZ : center S = ⊥) (hS : ReeTitsModel S .Tits 2 1)
    {V : Subgroup (MulAut S)} (hV : IsElemAbelian 3 V) (hc : Nat.card V = 27) : False := by
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2 := by
    obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hS
    have : Finite (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 F 0) :=
      Nat.finite_of_card_ne_zero
        (by rw [CFSG.RankThree.PartTwo.Census.Carrier.Tits.card_reeFixed hF]; norm_num)
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    exact (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num)
      (commutator _).subtype Subtype.val_injective).trans
      (CFSG.RankThree.PartTwo.Census.Carrier.Tits.pRank_three_reeFixed hF)
  obtain ⟨h2, -⟩ := CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier S 2 1 hS
  exact false_of_le_inner hZ hr hV hc
    (le_inner_of_not_three_dvd (not_three_dvd_card_outer_of_isPGroup_two h2) hV)

theorem false_of_m11
    {S : Type} [Group S] [Finite S] (hZ : center S = ⊥)
    (hS : NativeSporadic.IsSporadic S .M11) {V : Subgroup (MulAut S)} (hV : IsElemAbelian 3 V)
    (hc : Nat.card V = 27) : False := by
  have hr := pRank_three_eq_two_of_isSpor_M11 hS
  obtain ⟨a⟩ := hS
  have hout : Nat.card (Outer S) ≤ 2 := by
    rw [Nat.card_congr (equivalence a).toEquiv]
    exact CFSG.Sporadic.Schreier.at_m11_schreier.1
  exact false_of_le_inner hZ hr.le hV hc
    (le_inner_of_not_three_dvd (not_three_dvd_card_outer_of_le_two hout) hV)

theorem false_of_m12
    {S : Type} [Group S] [Finite S] (hZ : center S = ⊥)
    (hS : NativeSporadic.IsSporadic S .M12) {V : Subgroup (MulAut S)} (hV : IsElemAbelian 3 V)
    (hc : Nat.card V = 27) : False := by
  have hr := pRank_three_eq_two_of_isSpor_M12 hS
  obtain ⟨a⟩ := hS
  have hout : Nat.card (Outer S) ≤ 2 := by
    rw [Nat.card_congr (equivalence a).toEquiv]
    exact CFSG.ComponentClassification.M12Cover.card_outer.le
  exact false_of_le_inner hZ hr.le hV hc
    (le_inner_of_not_three_dvd (not_three_dvd_card_outer_of_le_two hout) hV)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListThree

end
