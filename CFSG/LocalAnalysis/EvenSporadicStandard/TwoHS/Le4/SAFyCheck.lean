module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyData

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def fyEq (u v : List ℕ) : Bool :=
  tblEq 11200 (wordTbl 11200 harYs u) (wordTbl 11200 harYs v)

@[expose] def fyC (i : ℕ) : List ℕ := fyCWords.getD i []

@[noinline, expose] def fyOK : Bool :=
  fyEq (fyRWord ++ fyRWord ++ fyRWord) [] && !fyEq fyRWord [] &&
  (List.range 4).all (fun i =>
    fyEq (fyC i ++ fyC i) tWord && fyEq (fyC i ++ fyRWord) (fyRWord ++ fyC i) &&
      fyEq (fyC i ++ fyAWord) (tWord ++ fyAWord ++ sigWord (fyC i))) &&
  (List.range 3).all (fun i =>
    fyEq (fyC i ++ fyC (i + 1) ++ fyC i) (fyC (i + 1) ++ fyC i ++ fyC (i + 1))) &&
  fyEq (fyC 0 ++ fyC 2) (fyC 2 ++ fyC 0) && fyEq (fyC 0 ++ fyC 3) (fyC 3 ++ fyC 0) &&
  fyEq (fyC 1 ++ fyC 3) (fyC 3 ++ fyC 1) &&
  fyEq (fyAWord ++ sigWord fyAWord) [] &&
  fyEq (fyAWord ++ sigWord fyRWord) (fyRWord ++ fyAWord) &&
  !fyEq (fyC 0) (fyC 1) && !fyEq (fyC 2) (fyC 0) && !fyEq (fyC 2) (fyC 0 ++ tWord) &&
  fyEq (fyLWord ++ fyAWord) (fyAWord ++ sigWord (fyC 0) ++ tWord ++ sigWord fyLWord)

end CFSG.EvenSporadicStandard.TwoHS
