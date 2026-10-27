module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4GamData

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.J4.Native CFSG.Quasithin.J4M2 CFSG.Sporadic.J4.QT2A

@[expose] def c0pLetRows : Array (Array V2) :=
  #[cArows, cBrows, cZrows, cAinvRows, cBinvRows, cZinvRows]

@[expose] def c0pWordRows (w : List ℕ) : Array V2 :=
  w.foldl (fun acc l => mulRows acc c0pLetRows[l]!) idRows

@[expose] def etaRows12 (c : ℕ) : Array V2 :=
  (List.range 12).foldl (fun acc j => if c.testBit j then mulRows acc gmats[j]! else acc) idRows

@[expose] def qNFRows (e : Bool) (c : ℕ) : Array V2 :=
  mulRows (if e then zM else idRows) (etaRows12 c)

@[expose] def kEltRows (f : Bool × ℕ × ℕ) : Array V2 :=
  mulRows (qNFRows f.1 f.2.1) (powRows cMat f.2.2)

@[expose] def q8MasksN : List ℕ := [0, 503, 3741, 3946]

@[expose] def k3FormsN : List (Bool × ℕ × ℕ) :=
  [false, true].flatMap fun e =>
    [(0, 0), (503, 0), (739, 2), (788, 2), (1160, 1), (1407, 1), (2581, 1), (3042, 1),
      (3198, 2), (3465, 2), (3741, 0), (3946, 0)].map fun ci => (e, ci.1, ci.2)

@[expose] def q8FormsN : List (Bool × ℕ) :=
  [false, true].flatMap fun e => q8MasksN.map fun c => (e, c)

@[expose] def k3Words : List (List ℕ) := [
    [], [1, 3, 4, 0, 0], [0, 1, 2, 3, 4, 2], [2, 3, 1, 3, 4, 3], [4, 0, 1, 1, 0, 5, 4],
    [1, 0, 0, 4, 5], [0, 0, 1, 0, 4, 5], [1, 0, 4, 0, 0, 5], [1, 2, 3, 4, 4, 3, 1],
    [0, 4, 0, 0, 5, 1], [2, 4, 0, 1, 0], [0, 0, 1, 3, 4], [0, 0, 1, 0, 1, 3, 4, 4],
    [0, 1, 0, 2, 4], [4, 0, 5, 1, 5], [1, 3, 3, 4, 2], [0, 5, 5, 5], [0, 1, 0, 4, 0, 5],
    [1, 1, 0, 4, 4, 5], [2, 4, 2, 3, 1], [2, 2, 2, 3], [1, 1, 3, 4, 4, 2], [0, 1, 3, 4, 0],
    [0, 2, 4, 0, 1]]

@[expose] def q8Words : List (List ℕ) := [
    [], [1, 3, 4, 0, 0], [2, 4, 0, 1, 0], [0, 0, 1, 3, 4], [0, 0, 1, 0, 1, 3, 4, 4],
    [0, 1, 0, 2, 4], [0, 1, 3, 4, 0], [0, 2, 4, 0, 1]]

@[expose] def c0pKWF : Bool :=
  wfR zM && wfR cMat && (List.range 12).all fun j => wfR gmats[j]!

@[noinline, expose] def c0pKOK : Bool :=
  c0pKWF && k3Words.length == 24 && k3FormsN.length == 24 && q8Words.length == 8 &&
    q8FormsN.length == 8 && (k3Words.all fun w => w.all fun l => decide (l < 6)) &&
    (q8Words.all fun w => w.all fun l => decide (l < 6)) &&
    (List.zip k3Words (k3FormsN.map kEltRows)).all (fun p => eqRows (c0pWordRows p.1) p.2) &&
    (List.zip q8Words (q8FormsN.map fun f => qNFRows f.1 f.2)).all
      (fun p => eqRows (c0pWordRows p.1) p.2) &&
    allDistinct (k3FormsN.map kEltRows) &&
    allDistinct (q8FormsN.map fun f => qNFRows f.1 f.2)

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
