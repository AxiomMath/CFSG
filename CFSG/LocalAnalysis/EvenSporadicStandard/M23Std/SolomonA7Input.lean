module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonGen

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open

@[expose] def SolomonZ2A7 : Prop :=
  SolomonGen (alternatingGroup (Fin 7))

end CFSG.EvenSporadicStandard.M23Std
