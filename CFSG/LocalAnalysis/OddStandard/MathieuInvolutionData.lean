module

public import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionSpec
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data

public section

namespace CFSG.OddStandard

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def m11Cg1 : List (Equiv.Perm (Fin 11)) :=
  m11CentWords1.map (evalCodes [m11gA, m11gB])

@[expose] def m11Specs1 : List WordRowSpec :=
  [⟨3, [1, 4], 8, [3], 4⟩]

@[expose] def m11Primes1 : List ℕ := [3]

@[expose] def m11Rec1 : InnerClassRecord 11 :=
  ⟨m11InvReps.getD 0 1, 165, 48, m11Cg1, m11Specs1.map (·.row m11Cg1)⟩

@[expose] def m11Records : List (InnerClassRecord 11) :=
  [m11Rec1]

@[expose] def m12Cg1 : List (Equiv.Perm (Fin 12)) :=
  m12CentWords1.map (evalCodes [m12gA, m12gB])

@[expose] def m12Specs1 : List WordRowSpec :=
  [⟨3, [-3, 4], 32, [3], 4⟩]

@[expose] def m12Primes1 : List ℕ := [3]

@[expose] def m12Rec1 : InnerClassRecord 12 :=
  ⟨m12InvReps.getD 0 1, 495, 192, m12Cg1, m12Specs1.map (·.row m12Cg1)⟩

@[expose] def m12Cg2 : List (Equiv.Perm (Fin 12)) :=
  m12CentWords2.map (evalCodes [m12gA, m12gB])

@[expose] def m12Specs2 : List WordRowSpec :=
  [⟨5, [-1], 24, [2, 3], 2⟩,
   ⟨3, [-3, -3], 20, [1], 2⟩]

@[expose] def m12Primes2 : List ℕ := [3, 5]

@[expose] def m12Rec2 : InnerClassRecord 12 :=
  ⟨m12InvReps.getD 1 1, 396, 240, m12Cg2, m12Specs2.map (·.row m12Cg2)⟩

@[expose] def m12Records : List (InnerClassRecord 12) :=
  [m12Rec1, m12Rec2]

@[expose] def m22Cg1 : List (Equiv.Perm (Fin 22)) :=
  m22CentWords1.map (evalCodes [m22gA, m22gB])

@[expose] def m22Specs1 : List WordRowSpec :=
  [⟨3, [-2], 32, [1], 2⟩]

@[expose] def m22Primes1 : List ℕ := [3]

@[expose] def m22Rec1 : InnerClassRecord 22 :=
  ⟨m22InvReps.getD 0 1, 1155, 384, m22Cg1, m22Specs1.map (·.row m22Cg1)⟩

@[expose] def m22Records : List (InnerClassRecord 22) :=
  [m22Rec1]

@[expose] def m23Cg1 : List (Equiv.Perm (Fin 23)) :=
  m23CentWords1.map (evalCodes [m23PermA, m23PermB])

@[expose] def m23Specs1 : List WordRowSpec :=
  [⟨7, [-4, 1], 192, [1], 2⟩,
   ⟨3, [-4, 3], 224, [1], 2⟩,
   ⟨7, [1, 4], 192, [1], 2⟩]

@[expose] def m23Primes1 : List ℕ := [3, 7]

@[expose] def m23Rec1 : InnerClassRecord 23 :=
  ⟨m23InvReps.getD 0 1, 3795, 2688, m23Cg1, m23Specs1.map (·.row m23Cg1)⟩

@[expose] def m23Records : List (InnerClassRecord 23) :=
  [m23Rec1]

@[expose] def m24Cg1 : List (Equiv.Perm (Fin 24)) :=
  m24CentWords1.map (evalCodes [m24gA, m24gB])

@[expose] def m24Specs1 : List WordRowSpec :=
  [⟨3, [-2, 1], 320, [1], 10⟩,
   ⟨5, [-1, -1], 384, [3], 6⟩]

@[expose] def m24Primes1 : List ℕ := [3, 5]

@[expose] def m24Rec1 : InnerClassRecord 24 :=
  ⟨m24InvReps.getD 0 1, 31878, 7680, m24Cg1, m24Specs1.map (·.row m24Cg1)⟩

@[expose] def m24Cg2 : List (Equiv.Perm (Fin 24)) :=
  m24CentWords2.map (evalCodes [m24gA, m24gB])

@[expose] def m24Specs2 : List WordRowSpec :=
  [⟨7, [-1], 1536, [2], 12⟩,
   ⟨7, [1], 1536, [2], 12⟩,
   ⟨3, [-2, -1, 2, 2, 1], 896, [2], 2⟩]

@[expose] def m24Primes2 : List ℕ := [3, 7]

@[expose] def m24Rec2 : InnerClassRecord 24 :=
  ⟨m24InvReps.getD 1 1, 11385, 21504, m24Cg2, m24Specs2.map (·.row m24Cg2)⟩

@[expose] def m24Records : List (InnerClassRecord 24) :=
  [m24Rec2, m24Rec1]

end CFSG.OddStandard
