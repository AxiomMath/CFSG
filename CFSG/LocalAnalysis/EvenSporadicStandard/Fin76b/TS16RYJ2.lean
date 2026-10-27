module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ2
public import Certificates.Certificate27810

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.Beta

theorem s16Model_t0_j2P :
    ∃ (ht : tp 315 (j2CentTbl 31) ∈ j2P) (hb : tp 315 (j2BetaTbl 7) ∈ j2P),
      S16Model ↥j2P ⟨tp 315 (j2CentTbl 31), ht⟩ ⟨tp 315 (j2BetaTbl 7), hb⟩ := by
  obtain ⟨e, he, -⟩ := ctuc_j2_full_automorphism_permutation_model
  obtain ⟨ht0, h0⟩ := rootFactsFor_t0_j2P
  exact S16.s16_model_of_check j2_groupData le_sup_left e he
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers j2u)) (fun _ => h0.card_E)
    Certificates.certificate27810.1

theorem s16ModelClass_j2P :
    S16ModelClass ↥j2P := by
  obtain ⟨ht0, hb7, hcomm, hβ⟩ := betaFor_j2P
  obtain ⟨ht1, hb1, hM⟩ := s16Model_t0_j2P
  obtain ⟨ht2, h0⟩ := rootFactsFor_t0_j2P
  refine S16ModelClass.of_class hM (fun t ht2 hs => exists_conj_t0 ht1 t ht2 hs) h0.card_cent ?_
    hβ.1
  exact mem_centralizer_singleton_iff.2 hcomm.symm

end CFSG.EvenSporadicStandard.Fin76b.J2
