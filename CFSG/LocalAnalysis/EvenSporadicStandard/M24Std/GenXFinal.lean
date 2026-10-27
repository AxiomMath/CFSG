module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.FirstHalf
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.GenXSection

public section

namespace CFSG.EvenSporadicStandard.M24Std.GenX

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem firstHalfProp :
    FirstHalfProp :=
  fun _ _ _ _ _ hs hcase => exists_firstHalf hs hcase

end CFSG.EvenSporadicStandard.M24Std.GenX
