module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheckData

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A CFSG.Quasithin.J4M2

@[expose] def rightC (X : Array V2) : Array V2 := mulT X cTab

@[expose] def leftC (X : Array V2) : Array V2 := mulT cMat (frTable X)

@[expose] def chkComm : Bool :=
  kTab.size == 24576 &&
    (List.range 24576).all fun n =>
      let X := kTab[n]!
      wfR X && wfR (rightC X) && wfR (leftC X) &&
        (!eqRows (rightC X) (leftC X) || decide ((decodeF n).2.1 = 0))

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck
