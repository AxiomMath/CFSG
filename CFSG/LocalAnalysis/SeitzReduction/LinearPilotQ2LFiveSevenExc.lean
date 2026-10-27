module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExE6
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExD4

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open RankOne (ExcTwoPartInput E6GraphTwoPartInput E7InnerTwoPartInput TrialityInnerTwoPartInput
  TwistedE6InnerTwoPartInput F4OrC4CentralQuotient)

theorem lFiveSevenListFamilyInput_of_twoPart {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) (h : ∀ f, ExcTwoPartInput t 7 f 6) :
    LFiveSevenListFamilyInput t := by
  intro S _ _ _ _ m f _ hSm τ hτ D hD hDm h2
  obtain rfl := RankOne.FiveEx.eq_zero_of_lieModel_exc ht hSm
  exact absurd (h f S hSm τ hτ) (sevenL3Group_of_hyp hD hDm h2).not_dvd

namespace SevenList

theorem sixteen_dvd_forty_nine_pow_sub_one (m : ℕ) : 2 ^ 4 ∣ 49 ^ m - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow 49 1 m
  rw [one_pow] at h
  exact (by norm_num : 2 ^ 4 ∣ 49 - 1).trans h

theorem sixteen_dvd_seven_pow_sq_sub_one (f : ℕ) : 2 ^ 4 ∣ (7 ^ f) ^ 2 - 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  exact sixteen_dvd_forty_nine_pow_sub_one f

end SevenList

section Families

theorem lFiveSevenListFamilyInput_G2 : LFiveSevenListFamilyInput .G2 :=
  lFiveSevenListFamilyInput_of_twoPart (by decide) fun f =>
    RankOne.excTwoPartInput_G2_of_pow (s := 4) (by norm_num) (by norm_num) (by norm_num)
      (SevenList.sixteen_dvd_seven_pow_sq_sub_one f) (by norm_num) le_rfl

theorem lFiveSevenListFamilyInput_E8 : LFiveSevenListFamilyInput .E8 :=
  lFiveSevenListFamilyInput_of_twoPart (by decide) fun _ =>
    RankOne.excTwoPartInput_E8 (by norm_num) (by norm_num) le_rfl

theorem lFiveSevenListFamilyInput_F4_of_odd (hodd : ∀ f, Odd f → ExcTwoPartInput .F4 7 f 6) :
    LFiveSevenListFamilyInput .F4 := by
  refine lFiveSevenListFamilyInput_of_twoPart (by decide) fun f => ?_
  rcases Nat.even_or_odd f with ⟨m, rfl⟩ | hf
  · refine RankOne.excTwoPartInput_F4 (s := 4) (by norm_num) (by norm_num) ?_ (by norm_num)
      le_rfl
    rw [← two_mul, pow_mul]
    exact SevenList.sixteen_dvd_forty_nine_pow_sub_one m
  · exact hodd f hf

theorem lFiveSevenListFamilyInput_E7_of_inner (hinner : ∀ f, E7InnerTwoPartInput 7 f 6) :
    LFiveSevenListFamilyInput .E7 :=
  lFiveSevenListFamilyInput_of_twoPart (by decide) fun f =>
    RankOne.excTwoPartInput_E7_of_inner (by norm_num) (by norm_num) le_rfl (hinner f)

namespace SevenList

theorem not_lieModel_PSL_three_one_of_f4OrC4 {L : Type} [Group L] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (h : F4OrC4CentralQuotient p f L) :
    ¬ LieModel (L ⧸ center L) .PSL 3 2 1 := by
  intro hA
  rcases h with h | h
  · have hadm : StatedLieAdmissible .F4 0 p f := ⟨hp, hf, rfl⟩
    obtain ⟨ht, -⟩ := eq_seven_of_lieModel_PSL_three_two hA hp2 hadm h
    exact absurd ht (by decide)
  · have hadm : StatedLieAdmissible .PSp 4 p f := ⟨hp, hf, by norm_num, fun h => by simp at h⟩
    obtain ⟨ht, -⟩ := eq_seven_of_lieModel_PSL_three_two hA hp2 hadm h
    exact absurd ht (by decide)

end SevenList

open CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.SteinbergCE in
theorem false_of_sevenL3_E6 {S : Type} [Group S] [Finite S] {m f : ℕ}
    (hSm : LieModel S .E6 m 7 f) {τ : MulAut S} (hτ : orderOf τ = 2)
    (hA : SevenL3Group (fixedSubgroup τ)) : False := by
  obtain rfl := RankOne.FiveEx.eq_zero_of_lieModel_exc (by decide) hSm
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6
    ((GH74.chevalleyExceptionalModel_of_lieModel (by decide) hSm).2 :
      UntwistedChevalleyModel S .E6 (7 ^ f))
  let e' : S ≃* adjointGroup TwistTag.E6.tag F := e
  have : Finite (adjointGroup TwistTag.E6.tag F) := Finite.of_equiv S e'.toEquiv
  let β : MulAut (adjointGroup TwistTag.E6.tag F) := MulAut.congr e' τ
  have hβ : orderOf β = 2 :=
    (orderOf_injective (MulAut.congr e').toMonoidHom (MulAut.congr e').injective τ).trans hτ
  have hAβ : SevenL3Group (fixedSubgroup β) := hA.congr e'
  rcases RankOne.two_pow_six_dvd_card_fixed_E6_or_graph (by norm_num) (by norm_num) hF β hβ with
    h | ⟨g, a, hga⟩
  · exact hAβ.not_dvd h
  · obtain ⟨⟨D, hD, hDm⟩, -⟩ := hAβ
    have hD' := RankOne.FiveEx.f4OrC4_of_isComponent_E6_graph F 7 f (by norm_num) (by norm_num)
      hF β g a hga hβ D hD
    exact SevenList.not_lieModel_PSL_three_one_of_f4OrC4 (by norm_num) (by norm_num)
      (RankOne.FiveEx.one_le_of_card hF) hD' hDm

theorem lFiveSevenListFamilyInput_E6 : LFiveSevenListFamilyInput .E6 :=
  fun _ _ _ _ _ _ _ _ hSm _ hτ _ hD hDm h2 =>
    (false_of_sevenL3_E6 hSm hτ (sevenL3Group_of_hyp hD hDm h2)).elim

theorem lFiveSevenListFamilyInput_twistedE6_of_inner
    (hinner : ∀ f, TwistedE6InnerTwoPartInput 7 f 6) :
    LFiveSevenListFamilyInput .twistedE6 := by
  intro S _ _ _ _ m f _ hSm τ hτ D hD hDm h2
  obtain rfl := RankOne.FiveEx.eq_zero_of_lieModel_exc (by decide) hSm
  have hA := sevenL3Group_of_hyp hD hDm h2
  by_cases hi : τ ∈ (MulAut.conj : S →* MulAut S).range
  · exact absurd (hinner f S hSm τ hτ hi) hA.not_dvd
  · have hadm := SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hSm
    exact (SevenList.not_lieModel_PSL_three_one_of_f4OrC4 (by norm_num) (by norm_num) hadm.2.1
      (RankOne.FiveEx.f4OrC4_of_isComponent_twistedE6_outer (by norm_num) (by norm_num) hadm hSm
        τ hτ hi D hD) hDm).elim

theorem lFiveSevenListFamilyInput_trialityD4_of_seven (h7 : TrialityInnerTwoPartInput 7 1 6) :
    LFiveSevenListFamilyInput .trialityD4 := by
  intro S _ _ _ _ m f _ hSm τ hτ D hD hDm h2
  obtain rfl := RankOne.FiveEx.eq_zero_of_lieModel_exc (by decide) hSm
  have hA := sevenL3Group_of_hyp hD hDm h2
  have hadm := SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hSm
  by_cases hi : τ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨d, -, hDd⟩ := RankOne.FiveEx.exists_lieModel_PSL_of_isComponent_trialityD4_inner
      (by norm_num) (by norm_num) hadm hSm τ hτ hi D hD
    obtain ⟨-, -, h7'⟩ := eq_seven_of_lieModel_PSL_three_two hDm (by norm_num)
      (SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hDd) hDd
    have hf1 : f = 1 := Nat.eq_one_of_mul_eq_one_right (SevenList.eq_one_of_seven_pow_eq_seven h7')
    subst hf1
    exact absurd (h7 S hSm τ hτ hi) hA.not_dvd
  · exact absurd (RankOne.two_pow_six_dvd_card_fixed_trialityD4_outer (by norm_num) (by norm_num)
      hSm τ hτ hi) hA.not_dvd

end Families

end CFSG.SeitzReduction.LinearPilot
