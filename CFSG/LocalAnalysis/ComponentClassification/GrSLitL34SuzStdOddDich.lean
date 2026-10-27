module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichSupport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichSingle
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichPairLift
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichPairOrd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichPairDiag
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichHost

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

section Certified


theorem l34SuzOddDichotomy_of_inputs
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hC5 : L3TwoPowProperFixedCatalog)
    (hcat : L34CyclicProperFixedCatalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple) (hSV : L34SuzSignalizerVanishing)
    (hCSuz : L34SuzCoreStepMirror) (hCField : L34FieldCoreStepMirror)
    (hSField : L34FieldStandardExclusion) (hEven : L34SuzEvenStandardExclusion)
    (hAS : RankTwoSporadic.SporadicCaseOdd .Suz)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (h25 : EvenSporadicStandard.Finkelstein77.Asc76Lemma25) :
    L34SuzOddDichotomy := by
  intro G _ _ A V K t y hS hD u hu hu1
  have ht : t ∈ centralizer ({u} : Set G) := mem_centralizer_of_l34SuzOdd hS hD hu
  have hW : ∀ F : Subgroup G, F ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 F →
      8 ≤ Nat.card F → wGroup F = ⊥ := fun F hFt hF hF8 =>
    wGroup_eq_bot_of_l34SuzOdd hSch hC4 hSV hS hFt hF hF8
  obtain ⟨hKt, hKn⟩ := normal_subgroupOf_of_l34SuzOdd hS hD hu hu1 ht
  have hs : orderOf (⟨t, ht⟩ : ↥(centralizer ({u} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hS.orderOf_t
  rcases l34SuzOddDich_support hcat (isKGroupCat_centralizer_of_l34SuzOdd hS hu1) hs hKt
      (isQuasisimple_subgroupOf_of_l34SuzOdd hD hu) hKn
      (odd_card_center_subgroupOf_of_l34SuzOdd hS hD hu)
      (isL34Type_subgroupOf_of_l34SuzOdd hD hu) with
    hsingle | ⟨L, hL, hKL, htype⟩ | ⟨L, hL, hLt, hLtype, hdiag, hsupp⟩
  · exact Or.inl (isComponent_of_isComponent_map_of_l34SuzOdd hSch hU hheld hW hS hD hu hu1 hsingle)
  · exact (false_of_host_of_l34SuzOdd hSch hC4 hC5 hCI hGA h13 hCSuz hCField hSField hEven hAS
      hCIT h25 hS hD hu hu1 hL hKL htype).elim
  · obtain ⟨P, E₁, a, hPD, hPL⟩ :=
      exists_l34SuzOddPairData hS hD hu hu1 ht hL hLt hLtype hdiag hsupp
    exact Or.inr (l34SuzSwappedAt_of_l34SuzOdd hS hD hu ht hLt hdiag hPD.le_centralizer
      (isComponent_of_l34SuzOddPairData hSch hU hheld hW hS hD hu hu1 hPD) hPL)

end Certified

end CFSG.ComponentClassification.GrSLit.L34Sec5S
