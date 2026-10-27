module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Fi22U62SubProof
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.EvenArm
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Hyp12LieCat
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterHolds
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArmsHolds

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.U62Odd

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
  CFSG.EvenSporadicStandard.Induction.Thm54Reach CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.UnitaryPilot CFSG.SeitzReduction.CrossChar
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

private theorem sporadicInnerRow_u62 {s : TauCeti.SporadicName}
    (hdvd : 9196830720 ∣ AGLEmbedding.sporOrd s)
    (h : SporadicInnerRow s 9196830720) : s = .Fi22 ∨ s = .Fi23 := by
  have hdvd' : 9196830720 ∣ sporOrder s := by
    rw [sporOrder_eq_sporOrd]
    exact hdvd
  rcases Hyp12Lie.dvd_sporOrder_u62 s hdvd' with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h (Hyp12Lie.not_innerRow_u62 (Or.inl rfl))
  · exact absurd h (Hyp12Lie.not_innerRow_u62 (Or.inr (Or.inl rfl)))
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd h (Hyp12Lie.not_innerRow_u62 (Or.inr (Or.inr (Or.inl rfl))))
  · exact absurd h (Hyp12Lie.not_innerRow_u62 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact absurd h (Hyp12Lie.not_innerRow_u62 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

private theorem sporadicOuterRow_u62 {s : TauCeti.SporadicName}
    (hdvd : 9196830720 ∣ AGLEmbedding.sporOrd s)
    (h : SporadicOuterRow s 9196830720) : s = .Fi24Prime := by
  cases s <;> first
    | exact absurd h (by simp only [SporadicOuterRow]; decide)
    | exact absurd hdvd (by simp only [AGLEmbedding.sporOrd]; decide)
    | exact rfl

private theorem alternating_arm {S : Type} [Group S] [Finite S] (hSimple : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a)
    (hAlt : ∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n)))
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (↥D ⧸ center ↥D) .PSU 6 2 1) : False :=
  catSUmAlternating S hSimple hna hAlt σ hσ 6 1 D (by norm_num) hD hDm

private theorem oddLie_arm
    {S : Type} [Group S] [Finite S] (hSimple : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hOdd : OddLieType S)
    {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (↥D ⧸ center ↥D) .PSU 6 2 1) : False := by
  have h64 := (catSUmOddLieAt_of_inputs CFSG.SeitzReduction.gls3OddLieAutComponentsInput
    (m := 6) (by norm_num)
    (sUmNotOddLieInputAt_of_lieOrderFormulas
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput 6)) S hSimple hna hOdd
    σ hσ 1 D hD hDm
  omega

private theorem evenLie_arm
    {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    (hSimple : IsSimpleGroup ↥N) (hna : ∃ a b : ↥N, a * b ≠ b * a)
    (hEven : EvenLieType ↥N) {P : Subgroup Y} (hP : SolStd P)
    (hq : CFSG.IsQuasisimple ↥P) (hPN : P ≤ N)
    {σ : MulAut ↥N} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)}
    (hD : IsComponent D)
    (hDP : D.map (fixedSubgroup σ).subtype = P.subgroupOf N)
    (hDm : LieModel (↥D ⧸ center ↥D) .PSU 6 2 1) : LieModel ↥N .PSL 6 2 2 := by
  by_cases hinn : σ ∈ (MulAut.conj : ↥N →* MulAut ↥N).range
  · exact (catSUmEvenInner ↥N hSimple hna hEven σ hσ hinn 6 1 D hD hDm).elim
  · have hfree : CFSG.SeitzReduction.F4Pilot.FixedCentralizerTwoFree σ D :=
      fixedCentralizerTwoFree_of_component armInputs_holds.evenInner hEven hP hq hPN hDP
    simpa using catSUmEvenOuterAt (m := 6) (by norm_num) ↥N hSimple hna hEven σ hσ hinn
      1 D hD hDm hfree


private theorem sporadic_arm {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    (hN : FStarSimple N) (hSpr : SporadicRep ↥N)
    {P : Subgroup Y} (hq : CFSG.IsQuasisimple ↥P) (hU : IsU62 (↥P ⧸ center ↥P))
    (hodd : Odd (Nat.card ↥(center ↥P))) (hPN : P ≤ N) {t : Y} (ht2 : orderOf t = 2)
    (hPt : P ≤ centralizer ({t} : Set Y))
    {σ : MulAut ↥N} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)}
    (hD : IsComponent D) (hDcard : Nat.card (↥D ⧸ center ↥D) = 9196830720) :
    IsSporadic ↥N .Fi23 ∨ IsSporadic ↥N .Fi24Prime := by
  have hSimple := hN.isSimpleGroup
  have hna := hN.nonabelian
  rcases hSpr with ⟨s, ⟨es⟩⟩
  obtain ⟨hdvd, hrowIn, hrowOut⟩ := armInputs_holds.table hSimple hna es hσ hD
  rw [hDcard] at hdvd hrowIn hrowOut
  by_cases hinn : σ ∈ (MulAut.conj : ↥N →* MulAut ↥N).range
  · rcases sporadicInnerRow_u62 hdvd (hrowIn hinn) with rfl | rfl
    ·
      exfalso
      obtain ⟨g⟩ := fi22U62Sub_proved Y N P hN.normal hN.centralizer_le ⟨es⟩ hPN
        ⟨t, ht2, hPt⟩ hq hU
      have hgcard : Nat.card (↥P ⧸ CFSG.oddCore ↥P) = 18393661440 := by
        rw [Nat.card_congr g.toEquiv, fi22D_card]
      have h2quot : 2 ^ 16 ∣ Nat.card (↥P ⧸ CFSG.oddCore ↥P) := by
        rw [hgcard]
        norm_num
      have h2P : 2 ^ 16 ∣ Nat.card ↥P :=
        h2quot.trans (Subgroup.card_quotient_dvd_card _)
      have hnot : ¬ 2 ^ 16 ∣ Nat.card ↥P := by
        intro hd
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥P)] at hd
        have hd' : 2 ^ 16 ∣ 9196830720 := by
          simpa [isU62_card hU] using
            (hodd.coprime_two_right.pow_right 16).symm.dvd_of_dvd_mul_right hd
        exact absurd hd' (by norm_num)
      exact hnot h2P
    · exact Or.inl ⟨es⟩
  · have hrow := sporadicOuterRow_u62 hdvd (hrowOut hinn)
    subst hrow
    exact Or.inr ⟨es⟩

theorem overgroup_of_catalog {Y : Type} [Group Y] [Finite Y] {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2) (hcat : CFSG.Blueprint.Catalog ↥N')
    {P : Subgroup Y} (hP : SolStd P) (hq : CFSG.IsQuasisimple ↥P)
    (hU : IsU62 (↥P ⧸ center ↥P)) (hodd : Odd (Nat.card ↥(center ↥P))) :
    LieModel ↥N' .PSL 6 2 2 ∨ IsSporadic ↥N' .Fi23 ∨ IsSporadic ↥N' .Fi24Prime := by
  haveI : N'.Normal := hN.normal
  have hSimple := hN.isSimpleGroup
  have hna := hN.nonabelian
  have hPN : P ≤ N' := Hyp.le_of_perfect_of_index_le_two hidx hq.1
  obtain ⟨t, ht2, hcomp⟩ := hP.exists_involution
  obtain ⟨σ, D, hσ, hD, hin, ⟨e⟩, hDP⟩ := exists_fixedComponent_conjNormal' hN ht2 hcomp hPN
  have eQ : ↥D ⧸ center ↥D ≃* ↥P ⧸ center ↥P := centerQuotientEquiv e
  have hPm : LieModel (↥P ⧸ center ↥P) .PSU 6 2 1 := isU62_lieModel hU
  have hDm : LieModel (↥D ⧸ center ↥D) .PSU 6 2 1 := LieModel.of_mulEquiv eQ.symm hPm
  have hDcard : Nat.card (↥D ⧸ center ↥D) = 9196830720 := by
    rw [Nat.card_congr eQ.toEquiv, isU62_card hU]
  rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition ↥N' hna).1 hcat with
    hAlt | hOdd | hEven | hSpr
  · exact (alternating_arm hSimple hna hAlt hσ hD hDm).elim
  · exact (oddLie_arm hSimple hna hOdd hσ hD hDm).elim
  · left
    exact evenLie_arm hSimple hna hEven hP hq hPN hσ hD hDP hDm
  · right
    exact sporadic_arm hN hSpr hq hU hodd hPN ht2 hcomp.1 hσ hD hDcard

end CFSG.EvenSporadicStandard.Induction.Fi.U62Odd
