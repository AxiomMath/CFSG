module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdDefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

theorem l34SuzOddStandardExclusion_of_inputs
    (hAS : RankTwoSporadic.SporadicCaseOdd .Suz)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (h25 : EvenSporadicStandard.Finkelstein77.Asc76Lemma25) (hD : L34SuzOddDichotomy)
    (hC : L34SuzOddNormalizerControl) (hW : L34SuzOddSwappedExclusion) :
    L34SuzOddStandardExclusion := by
  intro G _ _ hbase A hA hsuz hodd
  have hG : IsSimpleGroup G := hbase.1
  have hnonab : ∃ g h : G, g * h ≠ h * g := hbase.2.1
  have hK : Assembly.KProper Blueprint.Catalog G := hbase.2.2.1
  have hU : ¬ OutcomeLocal.UOutcome G := hbase.2.2.2.2.1
  have : IsSimpleGroup G := hG
  have hcard : ∀ S : Sylow 2 ↥(centralizer (A : Set G)), Nat.card S = 2 :=
    fun S => card_sylow_centralizer_eq_two_of_suz hAS hCIT h25 hnonab hK hU hA hsuz S
  obtain ⟨t, ht_mem, ht_order⟩ :=
    (CFSG.IsStandardSubgroup.standardComponentIsStandard hA).exists_involution_centralizer
  have hS : L34SuzOddSetting A t :=
    { base := hbase
      standard := hA
      suz := hsuz
      odd_card_center := hodd
      card_sylow := hcard
      orderOf_t := ht_order
      t_mem := ht_mem }
  obtain ⟨V, K, y, hDat⟩ := exists_l34SuzOddData hsuz hodd
  refine hW G A V K t y hS hDat fun u hu hu1 => ?_
  rcases hD G A V K t y hS hDat u hu hu1 with hcomp | hswap
  · exact absurd (hC G A V K t y hS hDat u hu hu1 hcomp)
      (not_centralizer_le_normalizer_of_l34SuzOdd hS hDat hu hu1)
  · exact hswap

end CFSG.ComponentClassification.GrSLit.L34Sec5S
