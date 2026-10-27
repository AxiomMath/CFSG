module

public import Certificates.Data.CFSGNative.Fi22.Classes

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.FrameJ

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi22.Native

set_option compiler.extract_closed false

@[expose] def fjDLeaf (a A B : Table) : Bool :=
  let P := compT 3510 A B
  invoOK 3510 P && !idOK 3510 P && order3OK 3510 (compT 3510 P a)

@[expose] def fjPairsOf (a : Table) (t0 t1 : Array Table) : List (Nat × Nat) :=
  (List.range t0.size).flatMap fun k =>
    ((List.range t1.size).filter fun j => fjDLeaf a t0[k]! t1[j]!).map fun j => (k, j)

@[expose] def fjDPairs (O : COrbit) : List (Nat × Nat) :=
  let L := sylLetters (chainLetters O)
  let T := chainTrees 3510 L sylBase
  fjPairsOf O.alpha (treeTabs 3510 T[0]! L) (treeTabs 3510 T[1]! L)

@[expose] def fjSylCheck (O : COrbit) : Bool := decide ((fjDPairs O).length ≤ 22)

@[expose] def fjSylCertificate : Bool := fjSylCheck (orbitData ())

end CFSG.EvenSporadicStandard.TwoFi22.FrameJ
