module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ2
public import Certificates.Certificate24612

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def uMulJ2 : ℕ → ℕ → ℕ := W16.mulE0

@[expose] def uIdxJ2 : ℕ := W16.eT

theorem uSpec_j2 : UTableSpec uMulJ2 uIdxJ2 :=
  Certificates.certificate24612.2

theorem uLabel_t0_j2P :
    ∃ ht : tp 315 (j2CentTbl 31) ∈ j2P, ∃ elt : ℕ → ↥j2P,
      ELabelling (rootGroup ↥j2P ⟨tp 315 (j2CentTbl 31), ht⟩)
        (⟨tp 315 (j2CentTbl 31), ht⟩ : ↥j2P) uMulJ2 uIdxJ2 elt :=
  Certificates.certificate24612.1

theorem uLabelClass_j2P :
    ULabelClass ↥j2P uMulJ2 uIdxJ2 := by
  obtain ⟨ht0, h0⟩ := uLabel_t0_j2P
  exact ULabelClass.of_class _ h0 (fun t ht2 hs => exists_conj_t0 ht0 t ht2 hs)

end CFSG.EvenSporadicStandard.Fin76b.J2
