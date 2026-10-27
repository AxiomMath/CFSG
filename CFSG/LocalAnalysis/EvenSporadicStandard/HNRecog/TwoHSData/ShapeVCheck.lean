module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIICheck

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def conjEqOK (c : List ℕ) (tx ty : Table) : Bool :=
  wordOK c && invOK 1408 (tabW c) (invT 1408 (tabW c)) && tblEq 1408 (conjTab c tx) ty

@[expose] def shapeD5OK : Bool :=
  wordOK fix5C.rep && commWordsOK d5Words (tabW fix5C.rep) && cayleyOK capS 120 d5Words imgD5

@[expose] def shapeUOK : Bool :=
  let tu := tabW u0Word
  gensOK && wordOK fix5B.rep && wordOK u0Word && primeOrderOK 2 tu && !tblEq 1408 tu (tabW wordA) &&
    commTT 1408 tu (tabW fix5B.rep) && conjEqOK c0Word (tabW wordZ₁) tu

@[expose] def rpConjOK (k : ℕ) (w : List ℕ) : Bool :=
  conjEqOK w (tabW fix5C.rep) (powT 1408 k (tabW rpWord))

@[expose] def shapeA8OK : Bool :=
  gensOK && wordOK fix5C.rep && wordOK rpWord && primeOrderOK 5 (tabW rpWord) &&
    commTT 1408 (tabW rpWord) (tabW wordB) && rpConjOK 1 (ckWords.getD 0 []) &&
    rpConjOK 2 (ckWords.getD 1 []) && rpConjOK 3 (ckWords.getD 2 []) &&
    rpConjOK 4 (ckWords.getD 3 [])

@[expose] def shapesVOK : Bool := shapeD5OK && shapeUOK && shapeA8OK

end CFSG.EvenSporadicStandard.HNRecog
