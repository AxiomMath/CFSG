module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6KleinCore

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.QuasithinUnique.A6Facts

theorem tauList_length : tauList.length = 24 := by decide +kernel

@[expose] def e3List : List (List Nat) :=
  tauList.filter fun c => Core.cpow c 3 == Core.cid && c != Core.cid

theorem aut_cent_check : Core.autL.all (fun b =>
    !(e3List.all fun e => Core.cmul b e == Core.cmul e b) || b == Core.cid || b == Core.tFrobC) =
      true := by
  decide +kernel

end CFSG.QuasithinUnique.DoubleA3
