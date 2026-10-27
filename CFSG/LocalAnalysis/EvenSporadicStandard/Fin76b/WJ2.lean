
module

public import CFSG.Sporadic.SmallOddCore.J2DataInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ2Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ2
public import Certificates.Certificate24608
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaSq
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelInvolutionFusion

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem rootFactsFor_t0_j2P :
    ∃ ht : tp 315 (j2CentTbl 31) ∈ j2P, RootFactsFor ↥j2P ⟨tp 315 (j2CentTbl 31), ht⟩ :=
  Certificates.certificate24608

theorem rootFactsClass_j2P :
    RootFactsClass ↥j2P := by
  obtain ⟨ht0, h0⟩ := rootFactsFor_t0_j2P
  exact RootFactsClass.of_class _ h0 (fun t ht2 hs => exists_conj_t0 ht0 t ht2 hs)

end CFSG.EvenSporadicStandard.Fin76b.J2
