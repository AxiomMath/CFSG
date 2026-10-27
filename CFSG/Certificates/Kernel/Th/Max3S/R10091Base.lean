
module

public import CFSG.Certificates.Kernel.Th.Gen.Max3
public import CFSG.Certificates.Kernel.Th.Spec.Big
public import CFSG.Sporadic.Schreier.LyBFS
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.Sporadic.Th.Max3.QuotientInputsBase

@[expose] public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec
open CFSG.ComponentClassification.PresentationLocal (CarmichaelIndex)
open CFSG.Sporadic.Th.Max3.AltQuot (carmCubeIdx carmPairIdx)

section Proofs

variable {D : CFSG.KC.Th.Gen.Max3Data} {A B : Array V4}

end Proofs

end CFSG.KC.Th.Max3S

end
