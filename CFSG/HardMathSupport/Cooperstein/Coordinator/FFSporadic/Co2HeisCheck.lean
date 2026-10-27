module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2SlpCheck
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2HeisData
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Schreier

set_option compiler.extract_closed false

@[expose] def heisBase (_ : Unit := ()) : Array (Array ℕ) := aArrs ++ #[zArr, tArr, uArr]

@[expose] def heisCheck (_ : Unit := ()) : Bool := slpOK (heisBase ()) heisSlp heisEqs heisNes

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2
