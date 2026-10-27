module

public import CFSG.Sporadic.SuzOddCore.CTICheckInputs
public import CFSG.Sporadic.SuzOddCore.InvGraphCheckInputs
public import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzData
public meta import CFSG.Sporadic.SuzOddCore.CTICheckInputs
public meta import CFSG.Sporadic.SuzOddCore.InvGraphCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzData

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native
  CFSG.PSL3Four.Native

@[expose, irreducible] def suzArr (w : List Int) : Array Nat := wordA 1782 bTriple bTripleInv w

@[expose, irreducible] def suzArrA : Array Nat := suzArr suzWordA

@[expose, irreducible] def suzArrB : Array Nat := suzArr suzWordB

@[expose, irreducible] def suzArrL : Array Nat := suzArr suzWordL

@[expose, irreducible] def suzArrAi : Array Nat := invCand 1782 suzArrA

@[expose, irreducible] def suzArrBi : Array Nat := invCand 1782 suzArrB

@[expose, irreducible] def suzArrLi : Array Nat := invCand 1782 suzArrL

@[expose] def suzArrAB : Array (Array Nat) := #[suzArrA, suzArrB]

@[expose] def suzArrABi : Array (Array Nat) := #[suzArrAi, suzArrBi]

@[expose, irreducible] def suzArrZ : Array Nat := wordA 1782 suzArrAB suzArrABi suzWordZ

@[expose] def suzConj (σ g : Array Nat) : Array Nat :=
  compA 1782 (compA 1782 σ g) (invCand 1782 σ)

@[expose, irreducible] def suzArrAl : Array Nat := suzConj suzArrL suzArrA

@[expose, irreducible] def suzArrBl : Array Nat := suzConj suzArrL suzArrB

@[expose, irreducible] def suzArrAli : Array Nat := invCand 1782 suzArrAl

@[expose, irreducible] def suzArrBli : Array Nat := invCand 1782 suzArrBl

@[expose] def suzArr4 : Array (Array Nat) := #[suzArrA, suzArrB, suzArrAl, suzArrBl]

@[expose] def suzArr4i : Array (Array Nat) := #[suzArrAi, suzArrBi, suzArrAli, suzArrBli]

@[expose, irreducible] def suzTabA : Tab := restrictArr (fixList 0) suzArrA

@[expose, irreducible] def suzTabB : Tab := restrictArr (fixList 0) suzArrB

@[expose, irreducible] def suzTabZ : Tab := restrictArr (fixList 0) suzArrZ

@[expose] def suzTabs : Array Tab := #[suzTabA, suzTabB]

@[expose] def suzGenCheck : Bool :=
  enumOK 42 suzTabs (enumOf 42 suzTabs 20160) && (enumOf 42 suzTabs 20160).tabs.size == 20160

@[expose] def suzClassCheck : Bool :=
  (List.range 10).all fun l =>
    l == 0 || l == 6 || comp 42 (classRep l) (classRep l) != idTab 42

@[expose] def suzLettersOK : Bool :=
  lettersOK 2 suzWordA && lettersOK 2 suzWordB && lettersOK 2 suzWordL &&
  lettersOK 2 suzWordZ && lettersOK 4 suzWordG0 && lettersOK 4 suzWordG1

@[expose] def suzInvOK : Bool :=
  isInvA 1782 suzArrA suzArrAi && isInvA 1782 suzArrB suzArrBi && isInvA 1782 suzArrL suzArrLi &&
  isInvA 1782 suzArrAl suzArrAli && isInvA 1782 suzArrBl suzArrBli

@[expose] def suzRelOK : Bool :=
  eqA 1782 (powA 1782 suzArrA 3) (idA 1782) && eqA 1782 (powA 1782 suzArrB 3) (idA 1782) &&
  eqA 1782 (tArr 0) b0Arr &&
  eqA 1782 (compA 1782 suzArrA (tArr 0)) (compA 1782 (tArr 0) suzArrA) &&
  eqA 1782 (compA 1782 suzArrB (tArr 0)) (compA 1782 (tArr 0) suzArrB) &&
  eqA 1782 (suzConj suzArrL (tArr 0)) (compA 1782 (tArr 0) suzArrZ) &&
  eqA 1782 (wordA 1782 suzArr4 suzArr4i suzWordG0) b0Arr &&
  eqA 1782 (wordA 1782 suzArr4 suzArr4i suzWordG1) b1Arr &&
  eqA 1782 (compA 1782 suzArrZ suzArrZ) (idA 1782)

@[expose] def suzFixOK : Bool :=
  fixedCountN 1782 suzArrZ == 54 && fixedCountN 1782 (tArr 0) == 42

@[expose] def suzZCheck : Bool := suzTabZ != idTab 42

@[expose] def suzRowCheck : Bool :=
  suzLettersOK && suzInvOK && suzRelOK && suzFixOK && suzGenCheck && suzClassCheck && suzZCheck

end CFSG.EvenSporadicStandard.Solomon78
