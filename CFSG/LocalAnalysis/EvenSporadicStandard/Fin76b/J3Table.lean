module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J3Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TableE

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.J3

@[expose] def sylIndex : Std.HashMap UInt64 ℕ := hashIndex 6156 sylList

@[expose] def sylIdx (x : Table) : ℕ := (sylIndex[hkey 6156 x]?).getD 128

@[expose] def mulTabJ3 : Array (Array ℕ) :=
  Array.ofFn (n := 128) fun a => Array.ofFn (n := 128) fun b =>
    sylIdx (compT 6156 sylList[a.val]! sylList[b.val]!)

@[expose] def mulJ3 (a b : ℕ) : ℕ := (mulTabJ3[a]!)[b]!

@[expose] def tIdxJ3 : ℕ := sylIdx t0

@[expose] def tableOK : Bool :=
  allIn 0 128 fun a => allIn 0 128 fun b =>
    decide (mulJ3 a b < 128) &&
      tblEq 6156 (compT 6156 sylList[a]! sylList[b]!) sylList[mulJ3 a b]!

@[expose] def j3E_check : Bool :=
  TableE.eCheck 128 mulJ3 tIdxJ3 && tableOK && decide (tIdxJ3 < 128) &&
    tblEq 6156 sylList[tIdxJ3]! t0 && tblEq 6156 sylList[0]! (idT 6156)

end CFSG.EvenSporadicStandard.Fin76b.J3
