module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableICheck

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel27

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def uSpec : List (ℕ × ℕ) := [(1, 1), (2, 2), (1, 4), (2, 1)]

@[expose] def vSpec : List (ℕ × ℕ) := [(1, 1), (2, 1), (1, 5), (2, 3)]

@[expose] def uWord : List ℕ := specWord classz.centGens uSpec

@[expose] def vWord : List ℕ := specWord classz.centGens vSpec

@[expose] def labU : Table := #[1, 0, 3, 2, 4]

@[expose] def labV : Table := #[2, 3, 0, 1, 4]

@[expose] def sqZ (x tz : Table) : Bool :=
  tblEq 1408 (compT 1408 x x) (idT 1408) || tblEq 1408 (compT 1408 x x) tz

@[expose] def commZ (x y tz : Table) : Bool :=
  tblEq 1408 (compT 1408 x y) (compT 1408 y x) ||
    tblEq 1408 (compT 1408 x y) (compT 1408 tz (compT 1408 y x))

@[expose] def liftOK : Bool :=
  let tz := tabW wordZ
  let tu := tabW uWord
  let tv := tabW vWord
  let L := subgroupList capI nWords1
  wordOK uWord && wordOK vWord && commTT 1408 tu tz && commTT 1408 tv tz &&
    blkMapOK 5 blkData1.blk tu labU && blkMapOK 5 blkData1.blk tv labV &&
    L.all fun n =>
      let x := compT 1408 tu n
      !sqZ x tz || L.all fun m =>
        let y := compT 1408 tv m
        !sqZ y tz || !commZ x y tz

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel27
