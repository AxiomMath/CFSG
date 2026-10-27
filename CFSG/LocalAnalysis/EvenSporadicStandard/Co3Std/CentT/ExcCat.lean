module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ExcO8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ExcU62
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ExcFi22

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Blueprint

section Certified


theorem ExcQuot.of_catalogue {Q : Type} [Group Q] [Finite Q]
    (h : LieModel Q .POmegaPlus 4 2 1 ∨ LieModel Q .PSU 6 2 1 ∨
      NativeSporadic.IsSporadic Q .Fi22) : ExcQuot Q := by
  rcases h with h | h | h
  · exact excQuot_o8 h
  · exact excQuot_u62 h
  · exact excQuot_fi22 h

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
