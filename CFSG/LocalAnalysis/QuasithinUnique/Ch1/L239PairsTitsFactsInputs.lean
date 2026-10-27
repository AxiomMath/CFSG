module

public import CFSG.Sporadic.Schreier.TitsBasic
public import CFSG.Sporadic.Schreier.TitsArrays

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits

@[expose] def aJ0 : Array ℕ := wordArr 1755 titsDerivedArrs [-4, -4]

@[expose] def aJ1 : Array ℕ := wordArr 1755 titsDerivedArrs [-4, 3, 3]

@[expose] def aJ2 : Array ℕ := wordArr 1755 titsDerivedArrs [3, 4, 3]

@[expose] def aK0 : Array ℕ := wordArr 1755 titsDerivedArrs [13]

@[expose] def aJy : Array ℕ := compA 1755 (compA 1755 aJ2 aJ0) aJ2

@[expose] def aKy1 : Array ℕ := compA 1755 (compA 1755 (compA 1755 aJ0 aK0) aK0) (invCand 1755 aJ0)

@[expose] def aKy2 : Array ℕ := compA 1755 (compA 1755 (compA 1755 (invCand 1755 aJ0) aK0) aK0) aJ0

@[expose] def aKy3 : Array ℕ :=
  compA 1755 (compA 1755 (compA 1755 (compA 1755 (compA 1755 aJ0 aJ0) aK0) aK0) aJ0) aJ0

@[expose] def aJc : Array ℕ := commArr 1755 aJ0 aJy

@[expose] def aKc1 : Array ℕ := commArr 1755 aK0 aKy1

@[expose] def aKc2 : Array ℕ := commArr 1755 aK0 aKy2

@[expose] def aKc3 : Array ℕ := commArr 1755 aK0 aKy3

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs
