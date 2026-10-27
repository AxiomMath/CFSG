module

public import CFSG.Sporadic.SmallOddCore.CentData

public section

namespace CFSG.GH74.Generic.S45

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native

structure PerfWit where
  comms : List (List Int × List Int)
  four : List Int

@[expose] def lettersOK (k : Nat) (w : List Int) : Bool := w.all fun l => l != 0 && l.natAbs ≤ k

@[expose] def invWord (w : List Int) : List Int := (w.map Neg.neg).reverse

@[expose] def pwLetter (n : Nat) (gs : Array Table) (l : Int) : Table :=
  if 0 < l then gs[l.toNat - 1]! else invT n gs[l.natAbs - 1]!

@[expose] def perfWitOK (n : Nat) (gs : List Table) (W : PerfWit) : Bool :=
  W.comms.length == gs.length && gs.all (fun g => permOK n g && invOK n g (invT n g)) &&
    (List.range gs.length).all (fun i =>
      lettersOK gs.length (W.comms[i]!).1 && lettersOK gs.length (W.comms[i]!).2 &&
        tblEq n gs.toArray[i]! (wordT n (pwLetter n gs.toArray)
          ((W.comms[i]!).1 ++ (W.comms[i]!).2 ++ invWord (W.comms[i]!).1 ++
            invWord (W.comms[i]!).2))) &&
    lettersOK gs.length W.four && ordTest n 4 (wordT n (pwLetter n gs.toArray) W.four)

end CFSG.GH74.Generic.S45
