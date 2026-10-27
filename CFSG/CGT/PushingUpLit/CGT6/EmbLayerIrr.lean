module

public import CFSG.CGT.PushingUpLit.CGT6.EmbIrr
public import CFSG.CGT.PushingUpLit.CGT6.EmbLayer

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem irrStep_holds : IrrStep := fun _ _ _ hV _ _ _ cfg _ => irr_of_cfg hV cfg

theorem step410_of_diag (hS : SchreierFor Assembly.InCatalog) (h47 : FourSeven)
    (hD : DiagFree) : Step410 :=
  step410_of_parts hS h47 hD irrStep_holds

end CFSG.CGT.PushingUpLit.CGT6
