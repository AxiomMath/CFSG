module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroSuzStd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroHost
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroTrans
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroProduct
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroCover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroDefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem false_of_isComponent_of_le_l34SuzOdd
    (hC : L34SuzOddNormalizerControl) (hSG : SuzTwoBFusionGeneration) {A : Subgroup G} {t : G}
    (hS : L34SuzOddSetting A t) {x : G} (hx : orderOf x = 2) (hxt : x * t = t * x)
    (hxA : x ∈ normalizer (A : Set G)) {P : Subgroup G} (hPA : P ≤ A)
    (hPx : P ≤ centralizer ({x} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({x} : Set G))))
    (hPodd : Odd (Nat.card (center ↥P))) (hPL : IsL34Type (↥P ⧸ center ↥P)) : False := by
  obtain ⟨V, y, u, hD, hu, hu1, rfl | rfl⟩ :=
    exists_l34SuzOddData_of_isComponent_of_l34SuzOdd hS hx hxt hxA hPA hPx hcomp hPodd hPL
  · exact not_centralizer_le_normalizer_of_l34SuzOdd hS hD hu hu1
      (hC G A V P t y hS hD _ hu hu1 hcomp)
  · exact false_of_isComponent_mul_of_l34SuzOdd hSG hS hD hu hu1 hcomp

theorem l34ZeroHostFree_of_inputs
    (hC : L34SuzOddNormalizerControl) (hSG : SuzTwoBFusionGeneration)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hC5 : L3TwoPowProperFixedCatalog)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple) (hCSuz : L34SuzCoreStepMirror)
    (hCField : L34FieldCoreStepMirror) (hSField : L34FieldStandardExclusion)
    (hEven : L34SuzEvenStandardExclusion) (hAS : RankTwoSporadic.SporadicCaseOdd .Suz)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (h25 : EvenSporadicStandard.Finkelstein77.Asc76Lemma25) (hG : L34BaseSetting G) :
    L34ZeroHostFree G := by
  intro x b hxb P hx hb hPx hPb hcomp hPodd hPL L hL hPLe hLx htype
  have hPq : IsQuasisimple ↥P :=
    (IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hPx)).mp hcomp.1
  rcases htype with hsuz | hrest
  · obtain ⟨M, hMb, hM, ⟨e⟩, hPM, hMx⟩ := exists_isPComponent_lift_of_isComponent hL
    have hPleM : P ≤ M := hPM P hPb hPq.1 hPLe
    have hMs : Blueprint.NativeSporadic.IsSporadic (↥M ⧸ Open.fusionZStar ↥M) .Suz := by
      obtain ⟨f⟩ := hsuz
      exact ⟨e.trans f⟩
    have hMr : 3 ≤ pRank 2 ↥M :=
      (three_le_pRank_of_l34Odd hPq hPodd hPL).trans (GrS5.pRank_le_of_le hPleM)
    exact false_of_isComponent_of_le_l34SuzOdd hC hSG
      (l34SuzOddSetting_of_isPComponent_suz hSch hC4 hCI hGA h13 hCSuz hEven hAS hCIT h25 hG hb
        hMb hM hMs hMr)
      hx (mem_centralizer_singleton_iff.mp hxb)
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hMx x hxb hLx)) hPleM hPx hcomp hPodd hPL
  · exact false_of_host_onan_field_of_l34 hSch hC5 hCI hGA h13 hCField hSField hG hb hPb hPq
      hPodd hPL hL hPLe hrest

end CFSG.ComponentClassification.GrSLit.L34Sec5S
