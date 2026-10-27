module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshSubCheck

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b

@[expose] def conjIn (nE : Array Table) (t₁ t₂ : Table) : Bool :=
  nE.any fun m => tblEq 16 (conjT 16 m t₁) t₂

theorem conjugatesTo_eq_conjIn (α k : ℕ) : conjugatesTo α k = conjIn (nEnum α k) := rfl

@[expose] def l6Core (nE : Array Table) (good : List Table) (eT : Table) (LE : List Table) : Bool :=
  LE.any fun y1 =>
    (nE.toList.filter (commTT 16 y1)).length == 128 &&
    LE.all fun T => !memTab 16 good T || conjIn nE eT T || conjIn nE y1 T

@[expose] def l6Check (α k : ℕ) : Bool :=
  l6Core (nEnum α k) (goodTabs α k) (nwT α k eWord) (tenum (wgens α k eWords)).toList

end CFSG.EvenSporadicStandard.M12Std.Yosh
