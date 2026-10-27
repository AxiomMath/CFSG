module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22GuestRankData

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Alt

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen.Native
open CFSG.AGLEmbedding.KFactProofs.Fi22Guest

set_option compiler.extract_closed false

@[expose] def xData : List (List Int) :=
  [[1, 13, -6, 8, 1, 13, -6, -8],
   [1, 13, -6, -6, 1, 13, -6, 6],
   [1, 13, -6, -14, 1, 13, -6, 14],
   [1, 13, -6, 11, 1, 13, -6, -11],
   [1, 13, -6, -9, 1, 13, -6, 9],
   [1, 13, -6, 6, 1, 13, -6, -6],
   [1, 13, -6, 4, 5, 1, 13, -6, -5, -4]]

@[expose] def xTab (n : Nat) (α αi β βi : Table) (i : Nat) : Table :=
  (xData.getD i []).foldr (fun s T => compT n (wordTab n α αi β βi (eLetterWord s)) T) (idT n)

@[expose] def mooreChecks (n : Nat) (X : Nat → Table) : Bool :=
  powT n 3 (X 1) == idT n &&
  (List.range 8).all (fun j => decide (j < 2) ||
    (powT n 2 (X j) == idT n && powT n 3 (compT n (X (j - 1)) (X j)) == idT n)) &&
  (List.range 8).all (fun i => (List.range 8).all fun j => decide (i < 1 ∨ j < i + 2) ||
    powT n 2 (compT n (X i) (X j)) == idT n) &&
  movesPt n (X 1)

@[noinline, expose] def altCheck (n : Nat) (α αi β βi : Table) : Bool :=
  let X1 := xTab n α αi β βi 0
  let X2 := xTab n α αi β βi 1
  let X3 := xTab n α αi β βi 2
  let X4 := xTab n α αi β βi 3
  let X5 := xTab n α αi β βi 4
  let X6 := xTab n α αi β βi 5
  let X7 := xTab n α αi β βi 6
  mooreChecks n fun i => [X1, X1, X2, X3, X4, X5, X6, X7].getD i X1

@[noinline, expose] def fi22AltCheck : Bool :=
  let O := CFSG.Sporadic.Fi22.Native.orbitData ()
  altCheck 3510 O.alpha O.alpha O.beta (invT 3510 O.beta)

end CFSG.AGLEmbedding.KFactProofs.Fi22Alt
