module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Defs
public import CFSG.LocalAnalysis.EvenBN.Common.StandardNormalClosure
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.Main
public import CFSG.LocalAnalysis.OddStandard.L2Ree.L2HalfHolds
public import CFSG.LocalAnalysis.OddStandard.HigherRank.Assemble
public import CFSG.LocalAnalysis.OddStandard.HigherRank.ClassicalFalseHolds
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Final

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.OddStandard

variable {G : Type} [Group G] [Finite G]

theorem oddCore_eq_bot_of_stdHyp {L : Subgroup G} (h : StdHyp G L) {z : G} (hz : orderOf z = 2) :
    CFSG.oddCore (centralizer ({z} : Set G)) = ⊥ := by
  rw [← LocalAnalysis.EvenBN.Common.standardComponentOddCore_eq_oddCore]
  exact h.oddCore z hz

theorem charThreeLie_of_smallF3LieQuotient {Q : Type} [Group Q]
    (h : CFSG.Yardstones.M0362f3a873a3.SmallF3LieQuotient Q) : CharThreeLie Q := by
  rcases h with h | h | h | h | h | h | h | h <;> exact ⟨_, _, _, h⟩

theorem centerClause_of_not_isMTypeSchur {L : Subgroup G} (hS : StandardSetting G L)
    (hlie : OddLieType (↥L ⧸ center ↥L))
    (hcase : Odd (Nat.card (center ↥L)) ∨
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ ComponentClassification.HarrisLit.IsMTypeSchur p L) :
    Odd (Nat.card (center ↥L)) ∨
      ∃ p n r : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < n ∧ 0 < r ∧
        (LieModel (↥L ⧸ center ↥L) .PSL (2 * n) p r ∨
          LieModel (↥L ⧸ center ↥L) .PSU (2 * n) p r) ∧
        ordProj[2] (Nat.card (center ↥L)) ≠
          ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥L ⧸ center ↥L))) := by
  by_cases hodd : Odd (Nat.card (center ↥L))
  · exact Or.inl hodd
  · refine Or.inr ?_
    have hnot : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ ComponentClassification.HarrisLit.IsMTypeSchur p L :=
      hcase.resolve_left hodd
    obtain ⟨t, n, p, f, hp, hp2, -, hm⟩ := hlie
    by_contra hne
    refine hnot p hp hp2 (isMTypeSchur_of_multiplier hS.standard
      (Nat.not_odd_iff_even.1 hodd) ⟨t, n, f, hm⟩ fun n' r hn hr hmod => ?_)
    by_contra hneq
    exact hne ⟨p, n', r, hp, hp2, hn, hr, hmod, hneq⟩

omit [Finite G] in
theorem oddOutcome_of_childOddLie
    (h : AltOutcome G ∨ OddLieType G ∨
      (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)) :
    OddOutcome G := by
  unfold OddOutcome
  tauto

section Certified

open _root_.Certificates


theorem oddLie_top_outcome
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    {X : Subgroup G} (hX : StdHyp G X) (hlie : OddLieType (↥X ⧸ center ↥X))
    (h5 : ¬ Nonempty (↥X ⧸ center ↥X ≃* alternatingGroup (Fin 5)))
    (h6 : ¬ Nonempty (↥X ⧸ center ↥X ≃* alternatingGroup (Fin 6)))
    (hF3 : ¬ CharThreeLie (↥X ⧸ center ↥X)) :
    AltOutcome G ∨ OddLieType G ∨
      (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS) := by
  have hCI : ComponentClassification.GSLit.ClassicalInvolutionInput := ci_of_cit hCIT
  have hS : StandardSetting G X := stdSetting_of_stdHyp hX
  obtain ⟨S, hcyc⟩ := hX.cyclicSylow
  by_cases hscope : HarrisSolomonFritzScope X
  · rcases oddLie_hsf (ComponentClassification.HSFLit.hsflit_of_steps hGH
      OddStandard.Harada75.haradaInput_holds
      (CFSG.ComponentClassification.GHarris.gorensteinHarrisInput_of
          (ThmC.leaf_of_full
              (ThmC.thmCFull_of_route ThmC.O2.o2Structure
                  (ThmC.Core.normalSimpleCore_of_hyps
                      (ThmC.O2.o2Structure_of_gor42 ThmC.O2.Gor.gor42) ThmC.O2.Gor.gor42)
                  (ThmC.simpleCase_of_gh74 hGH ThmC.sylowComparison) ThmC.l34IndexThree)
              ThmC.l34OneClass) CFSG.Quasithin.HSType.statementI48_holds)
      ComponentClassification.HSFLit.ghPresentationBound ComponentClassification.HSFLit.ghRelInHS
      ComponentClassification.HSFLit.Sec8.fritz812dNotSylow
      ComponentClassification.HSDihedral.FritzL2.fritzL2Lemma36Final
      ComponentClassification.HSDihedral.FritzL2.fritzL2Lemma378
      ComponentClassification.HSFLit.fritzL2KDFacts ComponentClassification.HSFLit.fritzKDSection4
      ComponentClassification.HSFLit.fritzKDSection6 ComponentClassification.HSFLit.fritzKDSection7
      (ComponentClassification.HSFLit.KD8ab.fritzKDSection8ab_of_cases
          CFSG.ComponentClassification.HSFLit.KD8ab.caseA
          CFSG.ComponentClassification.HSFLit.KD8abB.caseB)
      CFSG.ComponentClassification.HSFLit.KD8c.fritzKDSection8c) hS hscope S hcyc with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  by_cases hcase : Odd (Nat.card (center ↥X)) ∨
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ ComponentClassification.HarrisLit.IsMTypeSchur p X
  swap
  · push Not at hcase
    obtain ⟨hnodd, p, hp, hp2, hM⟩ := hcase
    have hH : ComponentClassification.HarrisLit.Harris82Theorem1SimpleKProperOdd :=
      ComponentClassification.HarrisLit.harris82Theorem1SimpleKProperOdd_of_row
        (ComponentClassification.HarrisLit.T1.harris82Theorem1KProper_of_ci hCI)
        ComponentClassification.HarrisLit.harris82SporadicRow
    exact Or.inr (Or.inl (oddLieType_of_isMTypeSchur_of_simpleKProperOdd hH hS
      (Nat.not_odd_iff_even.1 hnodd) hp hp2 hM))
  have hc := centerClause_of_not_isMTypeSchur hS hlie hcase
  by_cases hsmall : CFSG.Yardstones.M0362f3a873a3.SmallF3LieQuotient (↥X ⧸ center ↥X)
  · exact (hF3 (charThreeLie_of_smallF3LieQuotient hsmall)).elim
  by_cases hl2 : CFSG.Yardstones.M0362f3a873a3.L2OrReeLieQuotient (↥X ⧸ center ↥X)
  · rcases hl2 with hl2 | ⟨f, hf⟩
    · exact L2Ree.l2Half_of_milestones hGH hCI G X hS hlie hl2 h5 h6 hc S hcyc
    · exact (hF3 ⟨.twistedG2, 0, f, hf⟩).elim
  by_cases hcat : Catalog G
  · exact Or.inr (Or.inl (HigherRank.catalogCaseHolds_of_pumpLeaf
      ComponentClassification.GS82PumpInputs.chevOddPumpLeaf_holds G X hS hcat hlie hsmall hl2 h6))
  exfalso
  have hset : HigherRank.HRSetting G X :=
    ⟨hS, hcat, fun _ hz => oddCore_eq_bot_of_stdHyp hX hz, hlie, hsmall, hl2, h5, h6, hscope, hc,
      ⟨S, hcyc⟩⟩
  rcases HigherRank.hr_trichotomy hlie hsmall hl2 with hA | ⟨t, n, hm, -⟩ | hG23
  · exact HigherRank.classicalFalse_of_ci hCI
      (Solomon75.solomon2AnInput_of_gh74_of_caseNotA hGH Solomon75.caseNotA_false) G X hset hA
  · exact hF3 ⟨t, n, 1, hm⟩
  · exact hF3 ⟨.G2, 0, 1, hG23⟩

end Certified

end CFSG.EvenSporadicStandard.M12Std.Rbc
