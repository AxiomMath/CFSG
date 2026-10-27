module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaOrbData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaData

public section

namespace CFSG.ComponentClassification.AS81.Hexa

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow

@[expose] def hexaOrbCheck : Bool :=
  let T := eltsN 64 hexaTGens
  let M := eltsN 64 hexaMGens
  (List.range T.length).all fun i =>
    eqA 64 T[i]! (idA 64) ||
      (decide (hexaOrbW[i]! < M.length) &&
        (eqA 64 (conjA 64 M[hexaOrbW[i]!]! T[i]!) hexaT0 ||
          inLN 64 (eltsN 64 hexaR0Gens) (conjA 64 M[hexaOrbW[i]!]! T[i]!)))

end CFSG.ComponentClassification.AS81.Hexa
