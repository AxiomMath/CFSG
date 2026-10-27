module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6TwoTests
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6TwoTests

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.PairE6

open CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint
open CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two

@[expose] def nGenW (k : ℕ) : Native.Mat :=
  if rhoIdx.getD k 0 = k then Native.rootMat bracketCodes formBits (k + 6) true false
  else Native.mul (Native.rootMat bracketCodes formBits (k + 6) false true)
    (Native.rootMat bracketCodes formBits (rhoIdx.getD k 0 + 6) true true)

@[expose] def nGensP : Array Native.Mat := nGens ++ (List.range 72).toArray.map nGenW

@[expose] def progP : List (List ℕ) := [
    [62, 16, 61, 95, 8, 40, 106, 63, 44, 20, 40, 113, 124, 96, 125, 32, 43, 53, 63, 39, 58, 125,
      138, 128, 17, 62, 17, 128, 138, 125, 58, 39, 63, 53, 43, 32, 125, 96, 124, 113, 40, 20, 44,
      63, 106, 40, 8, 95, 61, 16],
    [17, 128, 138, 125, 58, 39, 63, 53, 43, 32, 125, 96, 124, 113, 40, 20, 44, 63, 106, 40, 8, 95,
      61, 16, 144, 144],
    [145, 145], [146, 146],
    [48, 66, 85, 110, 28, 67, 111, 118, 12, 98, 56, 97, 5, 15, 107, 86, 102, 21, 53, 5, 9, 9, 92,
      37, 130, 61, 48, 66, 61, 130, 37, 92, 9, 9, 5, 53, 21, 102, 86, 107, 15, 5, 97, 56, 98, 12,
      118, 111, 67, 28, 110, 85],
    [61, 130, 37, 92, 9, 9, 5, 53, 21, 102, 86, 107, 15, 5, 97, 56, 98, 12, 118, 111, 67, 28, 110,
      85, 148, 148, 148, 148, 148, 148],
    [149, 149], [150, 150], [151, 151],
    [48, 66, 45, 21, 99, 6, 91, 93, 52, 116, 3, 141, 48, 141, 117, 124, 89, 50, 21, 122, 29, 142,
      102, 94, 137, 25, 48, 66, 25, 137, 94, 102, 142, 29, 122, 21, 50, 89, 124, 117, 141, 48, 141,
      3, 116, 52, 93, 91, 6, 99, 21, 45],
    [25, 137, 94, 102, 142, 29, 122, 21, 50, 89, 124, 117, 141, 48, 141, 3, 116, 52, 93, 91, 6, 99,
      21, 45, 153, 153, 153],
    [154, 154], [155, 155], [156, 156],
    [48, 66, 132, 121, 80, 122, 140, 61, 39, 105, 143, 53, 73, 56, 16, 127, 68, 85, 54, 72, 123, 89,
      22, 61, 136, 60, 48, 66, 60, 136, 61, 22, 89, 123, 72, 54, 85, 68, 127, 16, 56, 73, 53, 143,
      105, 39, 61, 140, 122, 80, 121, 132],
    [60, 136, 61, 22, 89, 123, 72, 54, 85, 68, 127, 16, 56, 73, 53, 143, 105, 39, 61, 140, 122, 80,
      121, 132, 158, 158, 158, 158],
    [159, 159], [160, 160]
  ]

@[expose] def nValsP : Array Native.Mat := Native.slpRun nGensP progP

@[expose] def nU : Native.Mat := nGen 62

@[expose] def nV : Native.Mat := Native.mul (nGen 48) (nGen 66)

@[expose] def commB (P Q : Native.Mat) : Bool := Native.eqM (Native.mul P Q) (Native.mul Q P)

@[expose] def witOK (s : Native.Mat) (i m : ℕ) : Bool :=
  m % 2 == 1 && Native.eqM (Native.pow (nValsP.getD i Native.one) m) Native.one &&
    commB (nValsP.getD i Native.one) s

@[expose] def pairOK (s : Native.Mat) (w : List (ℕ × ℕ)) (P : Native.Mat) : Bool :=
  !(w.all fun q => commB (nValsP.getD q.1 Native.one) P) || Native.eqM P Native.one ||
    Native.eqM P s

@[expose] def candU (a0 a1 c : Bool) : Native.Mat :=
  Native.mul (Native.mul (Native.rootMat bracketCodes formBits 68 a0 a1)
    (Native.rootMat bracketCodes formBits 67 (a0 ^^ a1) a1))
    (Native.rootMat bracketCodes formBits 76 c false)

@[expose] def candV (a0 a1 c1 c2 c3 : Bool) : Native.Mat :=
  Native.mul (Native.mul (Native.mul (Native.mul
    (Native.rootMat bracketCodes formBits 58 a0 a1)
    (Native.rootMat bracketCodes formBits 54 (a0 ^^ a1) a1))
    (Native.rootMat bracketCodes formBits 72 c1 false))
    (Native.rootMat bracketCodes formBits 74 c2 false))
    (Native.rootMat bracketCodes formBits 76 c3 false)

@[expose] def witsU : List (ℕ × ℕ) := [(147, 3)]

@[expose] def witsV : List (ℕ × ℕ) := [(152, 3), (157, 3), (161, 3)]

@[expose] def bools : List Bool := [false, true]

@[expose] def pairCheckU : Bool :=
  witsU.all (fun q => witOK nU q.1 q.2) &&
    bools.all fun a0 => bools.all fun a1 => bools.all fun c => pairOK nU witsU (candU a0 a1 c)

@[expose] def pairCheckV : Bool :=
  witsV.all (fun q => witOK nV q.1 q.2) &&
    bools.all fun a0 => bools.all fun a1 => bools.all fun c1 => bools.all fun c2 =>
      bools.all fun c3 => pairOK nV witsV (candV a0 a1 c1 c2 c3)

end CFSG.ComponentClassification.RankTwoExceptional.PairE6
