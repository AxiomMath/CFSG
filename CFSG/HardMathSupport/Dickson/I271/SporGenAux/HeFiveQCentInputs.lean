module

public import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Monster.B.Mathieu.SylowCore

@[expose] public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.RankThree.Native
  CFSG.RankThree.PartOne

def heFiveQCentOK (_ : Unit := ()) : Bool :=
  let cC := heFiveC0Cert
  allLt cC.pts.size (fun k =>
    !(commA 8330 cC.pts[k]! heFiveQGens[0]! && commA 8330 cC.pts[k]! heFiveQGens[1]!) ||
      eqA 8330 (powArr 8330 cC.pts[k]! 5) (idA 8330))

end CFSG.HardMathSupport.Dickson.I271
