module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutEModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ3
public import Certificates.Certificate24611

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem autEFact_t0_j3P :
    ∃ ht : tp 6156 (j3CentTbl 9) ∈ j3P,
      AutEFact ↥(rootGroup ↥j3P ⟨tp 6156 (j3CentTbl 9), ht⟩) :=
  Certificates.certificate24611

theorem autEClass_j3P :
    AutEClass ↥j3P := by
  obtain ⟨ht0, h0⟩ := autEFact_t0_j3P
  exact AutEClass.of_class _ h0 (fun t ht2 _ => exists_conj_t0 ht0 t ht2)

end CFSG.EvenSporadicStandard.Fin76b.J3
