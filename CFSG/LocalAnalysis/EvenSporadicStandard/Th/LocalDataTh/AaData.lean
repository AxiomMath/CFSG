module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.NormData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Data

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

@[expose] def wG1 : List Gen := wordOfString "xyxyxy"

@[expose] def wG3 : List Gen := wordOfString "yxyxyxyyyyyxyyxyxyx"

@[expose] def wG4 : List Gen := wordOfString "xyyyxyxyxyyxyyxyxyyyyy"

@[expose] def rowsNfC (s n : ℕ) : Array V4 := rowsNf s (bitsOf n)

@[expose] def rowsG1 : Array V4 := mulRows (rowsNfC 1 50) (wordRows rowsX rowsY wG1)

@[expose] def rowsG2 : Array V4 := rowsNfC 0 45

@[expose] def rowsG3 : Array V4 :=
  mulRows (mulRows (rowsNfC 1 243) (wordRows rowsX rowsY wG3)) (rowsNfC 0 2)

@[expose] def rowsG4 : Array V4 :=
  mulRows (mulRows (rowsNfC 0 73) (wordRows rowsX rowsY wG4)) (rowsNfC 0 10)

@[expose] def rowsBe : Array V4 := rowsNfC 0 136

@[expose] def rowsPE (e : ℕ) : Array V4 :=
  mulRows (mulRows (mulRows (powRows rowsG1 (e % 2)) (powRows rowsG2 (e / 2 % 2)))
    (powRows rowsG3 (e / 4 % 2))) (powRows rowsG4 (e / 8 % 2))

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
