module

public import CFSG.Sporadic.HNOddCore.XCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.NatCheckInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native CFSG.Sporadic.He.Native CFSG.Sporadic.HNOddCore.Native

@[expose] def elevenWord : List Int := [-2, 1]

@[expose] def cyc11 : List Nat := [1, 11, 3, 6, 2, 0, 8, 7, 9, 10, 5, 4]

@[expose] def elevenFix : List Nat := [0, 88, 274750, 366789]

@[noinline, expose] def elevenChecksH (n : Nat) (hS : Array (Array Nat)) : Bool :=
  plettersOK 17 elevenWord && fixedSet n #[pword n hS (pinvs n hS) elevenWord] == elevenFix

@[noinline, expose] def elevenChecksR (n : Nat) (regs : Array (Array Nat)) : Bool :=
  elevenChecksH n (extendStrong n #[regs[1]!, regs[2]!] LocalData.strongWords)

@[noinline, expose] def elevenChecksO (O : VOrbit) : Bool :=
  elevenChecksR hnsData.n
    (progRegs hnsData.n (initRegs hnsData.n (natTab O.alpha) (natTab O.beta)) Data.subgroupProgram)

@[noinline, expose] def elevenNatCheck (_ : Unit := ()) : Bool :=
  natOK (extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2]
    LocalData.strongWords) (pinvs 12 (extendStrong 12 #[natArr LocalData.natGen1,
    natArr LocalData.natGen2] LocalData.strongWords)) elevenWord (natArr cyc11)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native
