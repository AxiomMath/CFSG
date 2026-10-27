module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10K
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Socle
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10U43
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonCatM10

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.EvenSporadicStandard


theorem catM10_of_arms (hI : A6InnerLieSmall) (hO : A6OuterLieSmall)
    (hZ : CFSG.EvenSporadicStandard.CatNoAlmostSimpleZ2 (alternatingGroup (Fin 6))) :
    CFSG.EvenSporadicStandard.CatM10AlmostSimple := by
  unfold CFSG.EvenSporadicStandard.CatM10AlmostSimple
  intro K _ _ S hSn hSs hcat hC z hz hfc hH
  haveI := hSn
  haveI := hSs
  obtain ⟨D, hDC, hDn, hDA, hzD, hcard, hinv, hsq⟩ := m10_unpack hz hfc hH
  have hna := nonabelian_of_centralizer_bot S hC
  have hsolv := CFSG.RankThree.PartOne.SPOR.schreierFor_catalog ↥S hna hcat
  have hDS : D ≤ S := perfect_le_socle S hC hsolv D hDA
  have cfg : M10Cfg S D z := ⟨hz, hDC, hDn, hDA, hzD, hcard, hinv, hsq, hDS⟩
  by_cases hzS : z ∈ S
  · exact (cfg.inner_false hI hZ hcat hC hzS).elim
  · obtain ⟨eX⟩ := cfg.outer_x0 hO hcat hC hzS
    have hz2 : z * z = 1 := by
      rw [← sq, ← hz]
      exact pow_orderOf_eq_one z
    have hdvd : Nat.card ↥(centralizer ({z} : Set K)) ∣ 4320 := by
      rw [hcard]
      norm_num
    obtain ⟨hidx, ⟨eK⟩⟩ := u43_identification S
      (eX.trans CFSG.EvenSporadicStandard.M24Std.CU43.psiEquiv) hC hz2 hdvd
      (cfg.no_order_six hzS)
    have hidx' : ∀ k : K, k ∈ S ∨ k * z ∈ S := by
      intro k
      by_cases hk : k ∈ S
      · exact Or.inl hk
      · refine Or.inr ((Subgroup.mul_mem_iff_of_index_two hidx).2 ?_)
        exact ⟨fun h => absurd h hk, fun h => absurd h hzS⟩
    exact ⟨m10_complement S hz hfc hzS hidx', Or.inr ⟨eK⟩⟩

end CFSG.ComponentClassification.CatFC
