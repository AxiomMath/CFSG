
module

public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ3Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ3
public import Certificates.Certificate24609
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaSq
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelInvolutionFusion

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem rootFactsFor_t0_j3P :
    ∃ ht : tp 6156 (j3CentTbl 9) ∈ j3P, RootFactsFor ↥j3P ⟨tp 6156 (j3CentTbl 9), ht⟩ :=
  Certificates.certificate24609

theorem rootFactsClass_j3P :
    RootFactsClass ↥j3P := by
  obtain ⟨ht0, h0⟩ := rootFactsFor_t0_j3P
  exact RootFactsClass.of_class _ h0 (fun t ht2 _ => exists_conj_t0 ht0 t ht2)

end CFSG.EvenSporadicStandard.Fin76b.J3
