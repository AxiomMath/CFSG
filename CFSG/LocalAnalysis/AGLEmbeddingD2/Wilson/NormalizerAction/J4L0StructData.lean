module

public import CFSG.Sporadic.Schreier.J4SData
public import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.J4M2.Orbit

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.J4.Native CFSG.Quasithin.J4M2 CFSG.Sporadic.J4.QT2A

@[expose] def lsHitWords : List (List ℕ) := [[14, 26, 22, 9, 28, 18, 17, 28, 31, 6, 19, 9, 9, 27, 28, 21, 29, 19, 3, 15, 19, 25, 4, 11], [31, 15, 10, 30, 15, 21, 1, 30, 27, 27, 21, 26, 17, 16, 13, 31, 12, 6, 31, 1, 1, 21, 30, 29, 23], [0, 18, 0, 14, 14, 17, 9, 11, 3, 19, 8, 28, 18, 13, 9, 29, 23, 22, 8, 13, 29, 30, 7, 6, 13, 23], [4, 11, 29, 7, 18, 9, 7, 11, 11, 17, 13, 24, 13, 20, 24, 28, 9, 22, 23, 7, 21, 16, 20, 24, 23, 5, 8, 18, 22, 16], [24, 30, 21, 0, 23, 22, 15, 3, 12, 5, 17, 11, 13, 12, 28, 23, 8, 20, 19, 7, 23, 9, 11, 8, 13, 24, 14, 15, 19, 11, 15], [20, 5, 23, 8, 26, 18, 5, 7, 1, 24, 17, 8, 19, 8, 18, 10, 25, 12, 9, 23, 20, 15, 7, 26, 6, 11, 8, 17, 27, 13, 26, 15, 6, 15, 31, 30, 0, 28, 22, 6, 21]]

@[expose] def lsHitRows (i : ℕ) : Array V2 :=
  (lsHitWords.getD i []).foldl (fun acc n => mulRows acc gmats[n]!) idRows

@[expose] def lsProdRows (idx : List ℕ) : Array V2 :=
  idx.foldl (fun acc i => mulRows acc (lsHitRows i)) idRows

@[expose] def lsAIdx : List ℕ := [4, 2, 5, 2, 5, 5, 5, 4]
@[expose] def lsBIdx : List ℕ := [5, 5, 1, 1, 5, 1, 3, 2]
@[expose] def lsAExp : ℕ := 2
@[expose] def lsBExp : ℕ := 3

@[expose] def lsARows (_ : Unit := ()) : Array V2 := powRows (lsProdRows lsAIdx) lsAExp
@[expose] def lsBRows (_ : Unit := ()) : Array V2 := powRows (lsProdRows lsBIdx) lsBExp

@[expose] def lsHitAt (i : ℕ) : Bool :=
  wfR (lsHitRows i) && eqRows (mulRows (lsHitRows i) cMat) (mulRows cMat (lsHitRows i))

@[expose] def lsOK (_ : Unit := ()) : Bool :=
  (List.range 6).all lsHitAt && decide (lsHitWords.length = 6) &&
    eqRows (powRows gmats[13]! 3) idRows &&
    eqRows (powRows (lsARows ()) 7) idRows && eqRows (powRows (lsBRows ()) 7) idRows &&
    eqRows (powRows (mulRows (lsARows ()) (lsBRows ())) 7) cMat

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
