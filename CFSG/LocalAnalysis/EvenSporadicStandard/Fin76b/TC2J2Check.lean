module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinEJ2Check

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open CFSG.ComponentClassification.J2Cover.Models

@[expose] def mulX (a d : ℕ) : ℕ :=
  if a < 128 then
    (if d < 128 then mulJ2 a d else 128 + mulJ2 a (d - 128))
  else
    (if d < 128 then 128 + mulJ2 (a - 128) (betaIdx d) else mulJ2 (a - 128) (betaIdx (d - 128)))

@[expose] def innX (a : ℕ) : Bool := decide (a < 128)

end CFSG.EvenSporadicStandard.Fin76b.J2
