module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.ChainTools
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Data
public import CFSG.Sporadic.Schreier.RuEnum
public import Certificates.Data.CFSGNative.Co3Schreier.Orbit

public section

namespace CFSG.ClassicalInvolution
namespace J3Proof

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier.Co3.Native CFSG.ClassicalInvolution.J3Data

@[expose] def zArr : Array ℕ := abArr[0]!

@[expose] def kLevels : Array Level := rawLevels 20520 kStrong kBase

@[expose] def uLevels : Array Level := rawLevels 20520 uStrong uBase

@[expose] def sLevels : Array Level := rawLevels 20520 sStrong sBase

@[expose] def selfCentTest (t : Array ℕ) : Bool :=
  !((List.range 4).all fun i => commutesA 20520 t uStrong[i]!) || siftA 20520 uLevels uBase 0 t

@[expose] def invTest (n : ℕ) (t : Array ℕ) : Bool :=
  eqA n (compA n t t) (idA n) && !eqA n t (idA n)

@[expose] def coverTest (t : Array ℕ) : Bool :=
  !(invTest 20520 t) || conjInvols.any fun c => eqA 20520 c t

@[expose] def fixZ : List ℕ := fixedList 20520 zArr

@[expose] def orbZ : Array (List ℕ) × Array ℕ × Array ℕ := hashSearch abArr fixZ 26163

end J3Proof
end CFSG.ClassicalInvolution
