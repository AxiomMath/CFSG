module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonGen

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

@[expose] def SolomonZ2A6 : Prop :=
  SolomonGen (alternatingGroup (Fin 6))

end CFSG.EvenSporadicStandard.Fin76b
