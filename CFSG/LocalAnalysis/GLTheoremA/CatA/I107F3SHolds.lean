module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3S67
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SU6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3STwE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA

theorem i1066Cover_holds
    : I1066Cover :=
  ⟨i1066CoverAt_F4, i1066CoverAt_U6, i1066CoverAt_twE6⟩

theorem coverEvenAt_holds
    : CoverEvenAt :=
  coverEvenAt_of_split i67Cover_holds i1066Cover_holds

end CFSG.LocalAnalysis.GLTheoremA
