module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

@[expose] def eichF (w u x : V6) : V6 :=
  x + bil x w • u + (bil x u + qm u * bil x w) • w

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
