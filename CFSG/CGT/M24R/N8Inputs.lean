module

public import CFSG.CGT.M24R.RelData
public import CFSG.Certificates.CosetTablePresented
public import CFSG.CGT.T75JM.N6Cols

public section

namespace CFSG.CGT.M24R

open CFSG.CosetTable CFSG.CGT.T75JM

abbrev carmRels8 := restrictWords (subsetOf 10 [0, 1, 2, 3, 4, 5]) relsN8Ten

@[expose] def modelCols8 : Fin 6 → Cols :=
  ![⟨10, 6, 2, 13⟩, ⟨14, 9, 3, 5⟩, ⟨15, 4, 6, 3⟩, ⟨11, 15, 7, 14⟩, ⟨4, 11, 5, 6⟩, ⟨5, 13, 1, 11⟩]

@[expose] def colsCode8 (C : Cols) : ℕ := C.c0 + 16 * C.c1 + 256 * C.c2 + 4096 * C.c3

@[expose] def colsOfCode8 (n : ℕ) : Cols := ⟨n % 16, n / 16 % 16, n / 256 % 16, n / 4096 % 16⟩

@[expose] def allCols8 : List Cols := (List.range 65536).map colsOfCode8

@[expose] def natEqB8 (n m : ℕ) : Bool := Nat.beq n m

@[expose] def isGL8 (C : Cols) : Bool := (List.range 15).all fun v => applyC C (v + 1) != 0

@[expose] def glCountCheck : Bool := natEqB8 (allCols8.filter isGL8).length 20160

@[expose] def evalM8 (w : List (Fin 6)) : Cols := w.foldr (fun i C => compC (modelCols8 i) C) idC

end CFSG.CGT.M24R
