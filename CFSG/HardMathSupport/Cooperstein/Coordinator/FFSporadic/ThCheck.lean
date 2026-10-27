module

public import CFSG.Sporadic.Th.Max3.AllConjInputsBase

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.AllConj

set_option compiler.extract_closed false

@[expose] def thDihWord : List ℕ := [2, 2, 1, 2, 1, 2]

@[expose] def thDihRows (_ : Unit := ()) : Array V4 :=
  mulRows rowsA (mulRows (mulRows (abRows thDihWord) rowsA) (abRows (invWord thDihWord)))

@[expose] def thDihCheck (_ : Unit := ()) : Bool :=
  eqRows (powRows (thDihRows ()) 19) idRows && !eqRows (thDihRows ()) idRows

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
