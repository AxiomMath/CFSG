module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22GuestRankData
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22GuestRankData

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.Fi22Cent

open CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen.Native

set_option compiler.extract_closed false

@[expose] def iC : Nat := 0

@[expose] def jC : Nat := 3

@[expose] def uData : List Int := [1, 2, -6, -13]

@[expose] def vData : List Int := [2, 11, -13, 6]

@[expose] def signedTab (n : Nat) (α αi β βi : Table) (l : List Int) : Table :=
  l.foldr (fun s T => compT n (wordTab n α αi β βi (eLetterWord s)) T) (idT n)

@[expose] def twoChecks (n : Nat) (U V Qi Qj : Table) : Bool :=
  powT n 3 U == idT n &&
  powT n 3 V == idT n &&
  compT n U V == compT n V U &&
  compT n U Qi == compT n Qi U &&
  compT n V Qj == compT n Qj V &&
  ([0, 1, 2].all fun a => [0, 1, 2].all fun b =>
    (a == 0 && b == 0) ||
      movesPt n (compT n (powT n a U) (powT n b V)))

@[noinline, expose] def centCheck (n : Nat) (α αi β βi : Table) : Bool :=
  relCheck n α αi β βi [wpow wx 5, wpow wy 5, wx ++ wy ++ winv wx ++ winv wy] &&
  movesPt n (wordTab n α αi β βi (qWord iC)) &&
  movesPt n (wordTab n α αi β βi (qWord jC)) &&
  twoChecks n (signedTab n α αi β βi uData) (signedTab n α αi β βi vData)
    (wordTab n α αi β βi (qWord iC)) (wordTab n α αi β βi (qWord jC))

@[noinline, expose] def fi22CentCheck : Bool :=
  let O := CFSG.Sporadic.Fi22.Native.orbitData ()
  centCheck 3510 O.alpha O.alpha O.beta (invT 3510 O.beta)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.Fi22Cent
