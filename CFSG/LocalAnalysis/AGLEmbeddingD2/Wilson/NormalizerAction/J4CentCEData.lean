module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4C0pKData

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.J4.Native CFSG.Quasithin.J4M2 CFSG.Sporadic.J4.QT2A

@[expose] def invWord : List ℕ :=
  [6, 15, 21, 21, 30, 4, 6, 2, 26, 10, 4, 6, 0, 8, 18, 14, 7, 27, 16, 12, 21, 24, 21, 5, 29, 18, 23, 23, 13, 20, 5, 29, 21, 31, 21, 7, 17, 22, 15]

@[expose] def invRows (_ : Unit := ()) : Array V2 :=
  invWord.foldl (fun acc n => mulRows acc gmats[n]!) idRows

@[expose] def invChk (_ : Unit := ()) : Bool :=
  eqRows (mulRows (invRows ()) cMat) (mulRows (mulRows cMat cMat) (invRows ())) &&
    (List.range 4096).all fun m =>
      m == 0 || ((!eqRows (mulRows (qNFRows false m) cMat) (mulRows cMat (qNFRows false m))) &&
        !eqRows (mulRows (qNFRows true m) cMat) (mulRows cMat (qNFRows true m)))

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
