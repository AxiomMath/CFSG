module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutEModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ2
public import Certificates.Certificate24610

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem autEFact_t0_j2P :
    ∃ ht : tp 315 (j2CentTbl 31) ∈ j2P,
      AutEFact ↥(rootGroup ↥j2P ⟨tp 315 (j2CentTbl 31), ht⟩) :=
  Certificates.certificate24610

theorem autEClass_j2P :
    AutEClass ↥j2P := by
  obtain ⟨ht0, h0⟩ := autEFact_t0_j2P
  exact AutEClass.of_class _ h0 (fun t ht2 hs => exists_conj_t0 ht0 t ht2 hs)

end CFSG.EvenSporadicStandard.Fin76b.J2
