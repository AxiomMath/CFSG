module

public import CFSG.LocalAnalysis.ComponentClassification.EvenStandardExceptionOddType
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverExclusionHolds
public import CFSG.Adapters.CatalogAgree
public import CFSG.Open.QTH13MaximalLocalTauCeti
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.KDCatHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenSmallLieMilestone
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.FS79Inner
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.TopAlt
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.TopM12Lie
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.TopM12Spor
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.TopStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Unconditional2

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Induction

variable {G : Type} [Group G] [Finite G]

section Certified

open _root_.Certificates


theorem topIsM12
    (hMcard : Nat.card CFSG.Open.MonsterY443Derived = CFSG.Open.monsterOrder)
    (hUG : Induction.Balance.UHered G)
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hGH : CFSG.ComponentClassification.UFrontier.GH74ModelsInput)
    (hCTE : CTEvenResidualStatement) (hL34 : Induction.ChildL34WHered)
    (hHe : Induction.ChildHeWHered) (h4 : M22M23M24Exclusion) (h5 : J1J3J4Exclusion)
    (h6 : HSMcLLyExclusion) (h7 : TwoHSGivesHN) (h8 : LargeExclusion) (h9 : Co2Exclusion)
    (h10 : TwoFi22Gives) (h11 : TwoBGivesM) (h12 : J2Exclusion)
    {L : Subgroup G} {t : G} (hO : Out G L t) : TopIsM12 G := by
  intro X hX hF
  have hNo : NoM12List G → False := fun h => hO.false_of_noM12List hMcard h
  have hCo3G : IsSporadic G .Co3 → False := fun h =>
    hO.outer (centralizer_le_sup_of_isSporadic_co3 hO.std hO.m12 h hO.mem hO.inv)
  have hCo3X : ¬ IsSporadic X .Co3 :=
    Co3Std.CentT.fs79Co3Excluded_of_catalog Co3Std.CentT.kdCo3Cat_holds G X hX
  have hSuz : Nat.card (center X) = 2 → ¬ IsSporadic (↥X ⧸ center ↥X) .Suz := fun h2 =>
    CFSG.EvenSporadicStandard.TwoSuz.twoSuz_not_standard_unconditional hX h2
  have hMJ : IsSporadic (↥X ⧸ center ↥X) .M12 ∨ IsSporadic (↥X ⧸ center ↥X) .J2 →
      center X = ⊥ := fun hQ => by
    haveI := hX.simple
    obtain ⟨S, hS⟩ := hX.cyclicSylow
    exact CFSG.ComponentClassification.StandardRecognition.center_eq_bot_of_m12_or_j2
      CFSG.ComponentClassification.StandardRecognition.m12J2DoubleCoverExclusion
      CFSG.ComponentClassification.StandardRecognition.m12J2CentralTwoGroupOrderBound
      hX.nonabelian
      (CFSG.Open.QTH13MaximalLocalTauCeti.kProper_inCatalog_of_agree
        CFSG.Open.QTFaithfulEmptyTauCeti.catalogAgree hX.kProper)
      hX.standard hX.oddCore S hS hX.centerTwo hQ
  have hSpor : SporadicRep (↥X ⧸ center ↥X) :=
    sporadicRep_of_stdHyp hCTE ctEvenSmallLieStatement_of_milestone
      (fun Y _ h => Recognition.Exact.evenStandardException_oddStandardType Y h) hL34 hHe hUG hNo
      hCo3G hX hF (fun hm hA => alt_top_outcome hCIT hGH h6 h7 hX hm hA)
      (fun hlie h5' h6' hF3 => oddLie_top_outcome hCIT hGH hX hlie h5' h6' hF3)
  exact isSporadic_m12_of_sporadicRep
    CFSG.EvenSporadicStandard.Frontier.child1_of_frontier
    CFSG.EvenSporadicStandard.Frontier.child2_of_frontier h4 h5 h6 h7 h8 h9 h10 h11 h12 hHe hUG
    hNo hX hCo3X hSuz hMJ hSpor

end Certified

end CFSG.EvenSporadicStandard.M12Std.Rbc
