module

public import Certificates.Data.CFSGNative.He.Certificate
public meta import Certificates.Data.CFSGNative.He.Certificate

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native

@[expose] def eqTab (n : Nat) (T T' : Table) : Bool := allIn 0 n fun i => ap T i == ap T' i

@[expose] def heWordE1 : List Int :=
  [
  -2, -1, -2, -2, -2, -2, -1, -2, -2, -2, 1, 2, 2, 2, 1, 2, 2, 1, 2, -1, -2, -2, -1, 2, 2, -1, -2,
  -2, -1, 2, 2, -1, -2, -2, -1, 2, 2, -1, 2, -1, -2, -2, -1, 2, 1, -2, 1, 2, 2, -1, -2, -2, -2, -2,
  1, -2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, -1]

@[expose] def heWordE2 : List Int :=
  [
  -2, -1, -2, -1, -2, -2, -2, -2, -2, -1, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -2, -2, -1, -2,
  -2, -1, 2, 2, -1, 2, -1, -2, -1, 2, -1, -2, -2, -2, -1, 2, 2, -1]

@[expose] def heWordE3 : List Int :=
  [
  -2, -2, -2, -1, 2, 2, -1, 2, 2, -1, 2, 2, 2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1,
  -2, -2, -2, -1, -2, -1, 2, 2, -1, -2, -1, -2, -2, -2, -1, -2, -1, 2, 2, 2, 1, 2, -1, 2, -1, 2,
  -1, 2, -1, 2, 2, -1, -2, -2]

@[noinline, expose] def heE8Check (O : VOrbit) : Bool :=
  let x := wordT 8330 (genTables O) heWordE1
  let y := wordT 8330 (genTables O) heWordE2
  let z := wordT 8330 (genTables O) heWordE3
  let one := idT 8330
  eqTab 8330 (compT 8330 x x) one && eqTab 8330 (compT 8330 y y) one &&
    eqTab 8330 (compT 8330 z z) one &&
    eqTab 8330 (compT 8330 x y) (compT 8330 y x) &&
    eqTab 8330 (compT 8330 x z) (compT 8330 z x) &&
    eqTab 8330 (compT 8330 y z) (compT 8330 z y) &&
    !eqTab 8330 x one && !eqTab 8330 y one && !eqTab 8330 y x && !eqTab 8330 z one &&
    !eqTab 8330 z x && !eqTab 8330 z y && !eqTab 8330 z (compT 8330 x y)

end CFSG.EvenSporadicStandard.Induction
