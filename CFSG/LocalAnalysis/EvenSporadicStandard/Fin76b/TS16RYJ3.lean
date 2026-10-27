module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ3
public import Certificates.Certificate27810

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.Beta

theorem s16Model_t0_j3P :
    ∃ (ht : tp 6156 (j3CentTbl 9) ∈ j3P) (hb : tp 6156 (j3BetaTbl 7) ∈ j3P),
      S16Model ↥j3P ⟨tp 6156 (j3CentTbl 9), ht⟩ ⟨tp 6156 (j3BetaTbl 7), hb⟩ := by
  obtain ⟨e, he, -⟩ := ctuc_j3_full_automorphism_permutation_model
  obtain ⟨ht0, h0⟩ := rootFactsFor_t0_j3P
  exact S16.s16_model_of_check j3_groupData le_sup_left e he
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers j3u)) (fun _ => h0.card_E)
    Certificates.certificate27810.2

theorem s16ModelClass_j3P :
    S16ModelClass ↥j3P := by
  obtain ⟨ht0, hb7, hcomm, hβ⟩ := betaFor_j3P
  obtain ⟨ht1, hb1, hM⟩ := s16Model_t0_j3P
  obtain ⟨ht2, h0⟩ := rootFactsFor_t0_j3P
  refine S16ModelClass.of_class hM (fun t ht2 hs => ?_) h0.card_cent ?_ hβ.1
  · exact exists_conj_t0 ht1 t ht2
  · exact mem_centralizer_singleton_iff.2 hcomm.symm

end CFSG.EvenSporadicStandard.Fin76b.J3
