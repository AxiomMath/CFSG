module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYHsData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSFiveData

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.EvenSporadicStandard.HSStd.FiveY

@[expose] def involA (a : Array ℕ) : Bool :=
  eqA 100 (compA 100 a a) (idA 100) && !eqA 100 a (idA 100)

@[expose] def fixedA (a : Array ℕ) : Bool := (List.range 100).any fun i => a[i]! == i

@[expose] def adjA (b c : Array ℕ) : Bool := involA (compA 100 b c)

@[expose] def nbrL : List (Array ℕ) := x3Cert.pts.toList.filter fun b => adjA x3 b

@[expose] def cliqueOK : Bool :=
  validA 100 Zassenhaus.HSFive.u0 &&
    (List.range 100).all (fun i => Zassenhaus.HSFive.u0[i]! != i) &&
    nbrL.all fun b =>
      fixedA (compA 100 x3 b) ||
        (let L := nbrL.filter fun c => adjA b c
         L.all fun c => L.all fun d => !adjA c d)

end CFSG.EvenSporadicStandard.HSStd.PumpHS
