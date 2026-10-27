module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open CFSG.ComponentClassification.J2Cover.Models

@[expose] def j2SylowCheck : Bool :=
  (List.range 128).all (fun a => mulIdx a 4 == mulIdx 4 a) &&
    (List.range 128).all (fun a =>
      !((List.range 128).all fun d => mulIdx a d == mulIdx d a) || a == 0 || a == 4) &&
    (mulIdx 1 1 == 4)

end CFSG.EvenSporadicStandard.Fin76b.J2
