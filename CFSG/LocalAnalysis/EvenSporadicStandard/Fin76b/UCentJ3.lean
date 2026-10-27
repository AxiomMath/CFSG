module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaJ3
public import Certificates.Certificate24613

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def uMulJ3 : ℕ → ℕ → ℕ := W16.mulEJ3

@[expose] def uIdxJ3 : ℕ := W16.eT

theorem uSpec_j3 : UTableSpec uMulJ3 uIdxJ3 :=
  Certificates.certificate24613.2

theorem uLabel_t0_j3P :
    ∃ ht : tp 6156 (j3CentTbl 9) ∈ j3P, ∃ elt : ℕ → ↥j3P,
      ELabelling (rootGroup ↥j3P ⟨tp 6156 (j3CentTbl 9), ht⟩)
        (⟨tp 6156 (j3CentTbl 9), ht⟩ : ↥j3P) uMulJ3 uIdxJ3 elt :=
  Certificates.certificate24613.1

theorem uLabelClass_j3P :
    ULabelClass ↥j3P uMulJ3 uIdxJ3 := by
  obtain ⟨ht0, h0⟩ := uLabel_t0_j3P
  exact ULabelClass.of_class _ h0 (fun t ht2 _ => exists_conj_t0 ht0 t ht2)

end CFSG.EvenSporadicStandard.Fin76b.J3
