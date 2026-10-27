module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TableE

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open CFSG.ComponentClassification.J2Cover.Models

@[expose] def j2ECheck : Bool :=
  TableE.eCheck 128 mulIdx 4 &&
    (TableE.eList 128 mulIdx 4).all fun a =>
      decide (a < 128) && (!(mulIdx a a == 0 && a != 0) || fixCountArr eltArrs[a]! == 11)

end CFSG.EvenSporadicStandard.Fin76b.J2
