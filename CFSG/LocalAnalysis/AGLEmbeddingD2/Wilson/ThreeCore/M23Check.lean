module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Check
public import CFSG.Sporadic.Schreier.CountSpec

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M23

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

abbrev gA : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

abbrev gB : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

@[expose] def letG (l : ℤ) : Equiv.Perm (Fin 23) :=
  if l = 1 then gA else if l = -1 then gA⁻¹ else if l = 2 then gB else gB⁻¹

@[expose] def letT (l : ℤ) : Table := toTable (letG l)

@[expose] def wT (w : List ℤ) : Table := wordT 23 letT w

@[expose] def xW : List ℤ :=
  [-1, 2, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, -1, -2, -2, -1, -2, -1, 2, -1, -2, -2, -1, 2, -1, -2,
   -1, -2, -2, -2, 1, 2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1]

@[expose] def yW : List ℤ :=
  [2, 1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -1, -2, -2, -1, 2,
   -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2,
   -1, -2, -2, -1, 2, -1, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, -1, 2, -1, 2]

@[expose] def c1W : List ℤ :=
  [-1, -2, -1, -2, -1, -2, -2, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1]

@[expose] def c2W : List ℤ :=
  [-2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2,
   1, 2, 1, 2, 1, 2]

@[expose] def r0W : List ℤ :=
  [-1, -2, -1, -2, -1, -2, -2, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1]

@[expose] def h0W : List ℤ :=
  [-2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2,
   1, 2, 1, 2, 1, 2, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2,
   1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2]

@[expose] def r1W : List ℤ :=
  [-2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2,
   1, 2, 1, 2, 1, 2, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2,
   1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2,
   -2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2]

@[expose] def h1W : List ℤ :=
  [-1, -2, -1, -2, -1, -2, -2, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, -2, -1,
   -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2,
   1, 2, 1, 2, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2, 1, 2,
   2, 2, 1, 2, 1, 2, 1, 2, 1, 2, -1, -2, -1, -2, -1, -2, -2, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2,
   2, 2, 1, 2, 1, 2, 1]

@[expose] def r2W : List ℤ :=
  [-2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2,
   1, 2, 1, 2, 1, 2, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2,
   1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, -1, -2, -1, -2, -1, -2, -2, -2, -1, -2, -1, -2, 1, 2, 1, 2,
   1, 2, 2, 2, 1, 2, 1, 2, 1, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, 1, 2,
   2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2]

@[expose] def h2W : List ℤ :=
  [-2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2,
   1, 2, 1, 2, 1, 2]

@[expose] def m23Words : List (List ℤ) := [xW, yW, c1W, c2W, r0W, r1W, r2W, h0W, h1W, h2W]

@[expose] def m23Sift (T : Table) : Bool := m23Words.any fun w => tblEq 23 T (wT w)

@[expose] def m23Pg : Array Table := #[toTable gA, toTable gB]

@[expose] def m23PgInv : Array Table := #[toTable gA⁻¹, toTable gB⁻¹]

@[expose] def m23Row : ClassRow where
  rep := wT xW
  outer := false
  classSize := 56672
  centOrder := 180
  centGens := [wT c1W, wT c2W]
  oddPrimes := [2, 5]
  odd := [⟨wT r0W, 2, 15, .conj (wT h0W) 3⟩,
      ⟨wT r1W, 5, 12, .conj (wT h1W) 3⟩,
      ⟨wT r2W, 5, 12, .conj (wT h2W) 3⟩]

set_option compiler.extract_closed false in
@[noinline, expose] def m23ThreeCheck : Bool :=
  threeDataOK 23 10200960 60000 m23Pg m23PgInv m23Sift [wT xW, wT yW] 9 [m23Row]

end CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M23
