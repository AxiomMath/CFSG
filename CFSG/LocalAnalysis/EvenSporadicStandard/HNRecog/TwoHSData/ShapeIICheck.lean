module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIIData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CayleyCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixData

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def capS : ℕ := 100000

@[expose] def shape3OK : Bool :=
  let tr := tabW fix3.rep
  let LY := subgroupList capS y3Words
  let LN := subgroupList capS n3Words
  let LV := subgroupList capS v3Words
  let LA := subgroupList capS a3Words
  wordOK fix3.rep && primeOrderOK 3 tr && enumW capS 480 y3Words && enumW capS 240 n3Words &&
    enumW capS 4 v3Words && enumW capS 60 a3Words && commWordsOK y3Words tr &&
    !memT 1408 LY tr && wordsInOK LY n3Words && wordsInOK LN v3Words && wordsInOK LN a3Words &&
    commPairsOK v3Words n3Words && trivInterOK (idT 1408) LV LA && sqOneOK (idT 1408) LV &&
    blkDataOK blkDataA3 && blkImageOK blkDataA3 60

@[expose] def shape5AOK : Bool :=
  let tr := tabW fix5A.rep
  let LN := subgroupList capS n5Words
  wordOK fix5A.rep && fix5A.cent.all wordOK && enumW capS 125 n5Words &&
    commWordsOK n5Words tr && commWordsOK s5Words tr && powOneOK 5 (idT 1408) LN &&
    normGensOK LN fix5A.cent n5Words &&
    !commTT 1408 (tabW (n5Words.getD 0 [])) (tabW (n5Words.getD 2 [])) &&
    cayleyOK capS 16 s5Words imgS5

@[expose] def shape5BOK : Bool :=
  wordOK fix5B.rep && commWordsOK b5Words (tabW fix5B.rep) && cayleyOK capS 100 b5Words imgB5

@[expose] def shape5COK : Bool :=
  let tr := tabW fix5C.rep
  let ta := tabW wordA
  let tu := tabW u5Word
  let tv := tabW v5Word
  let LY := subgroupList capS y5Words
  wordOK fix5C.rep && primeOrderOK 5 tr && wordOK u5Word && wordOK v5Word &&
    enumW capS 240 y5Words && commWordsOK y5Words tr && !memT 1408 LY tr && memT 1408 LY ta &&
    memT 1408 LY tu && memT 1408 LY tv && blkDataOK blkDataY5 && blkImageOK blkDataY5 120 &&
    blkTrivOK blkDataY5.blk ta && commutatorEqOK tu tv ta

@[expose] def shape7OK : Bool :=
  let tr := tabW fix7.rep
  let tw := tabW w7Word
  gensOK && wordOK fix7.rep && primeOrderOK 7 tr && wordOK w7Word && fix7.cent.all wordOK &&
    primeOrderOK 2 tw && commWordsOK [w7Word] tr && commWordsOK fix7.cent tw &&
    !tblEq 1408 tw (tabW wordA)

@[expose] def shapesIIOK : Bool := shape3OK && shape5AOK && shape5BOK && shape5COK && shape7OK

end CFSG.EvenSporadicStandard.HNRecog
