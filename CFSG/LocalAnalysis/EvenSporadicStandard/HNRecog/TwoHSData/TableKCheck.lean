module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKData

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def capK : ℕ := 100000

@[expose, noinline] def centInOK (L : Array Table) (gs : List Table) (M : Array Table) : Bool :=
  L.all fun s => !(gs.all fun g => commTT 1408 s g) || memT 1408 M s

@[expose, noinline] def centInPairOK (L : Array Table) (gs : List Table) (idt tc : Table) : Bool :=
  L.all fun s => !(gs.all fun g => commTT 1408 s g) || tblEq 1408 s idt || tblEq 1408 s tc

@[expose, noinline] def commListsOK (gs hs : List Table) : Bool :=
  gs.all fun g => hs.all fun h => commTT 1408 g h

@[expose, noinline] def prodCoverOK (L Z Q : Array Table) : Bool :=
  L.all fun s => Z.any fun z => Q.any fun q => tblEq 1408 (compT 1408 z q) s

@[expose, noinline] def commInOK (L : Array Table) (tc : Table) : Bool :=
  L.all fun s => L.all fun t =>
    tblEq 1408 (compT 1408 s t) (compT 1408 t s) ||
      tblEq 1408 (compT 1408 s t) (compT 1408 tc (compT 1408 t s))

@[expose, noinline] def sqInPairOK (L : Array Table) (idt tc : Table) : Bool :=
  L.all fun s => tblEq 1408 (compT 1408 s s) idt || tblEq 1408 (compT 1408 s s) tc

@[expose] def tableK1OK : Bool :=
  let tz := tabW wordZ
  blkDataOK blkDataK && blkImageOK blkDataK 120 && enumW capK 15360 kWords &&
    kWords.all (fun w => preservesHalves (tabW w)) &&
    kWords.all (fun w => commTT 1408 (tabW w) tz) && wordOK (classz.centGens.getD 1 []) &&
    swapsZero (tabW (classz.centGens.getD 1 []))

@[expose] def tableK2OK : Bool :=
  let nt := nWordsK.map tabW
  let NL := subgroupList capK nWordsK
  let ZL := subgroupList capK zcWordsK
  let tx := tabW xWordK
  let ty := tabW yWordK
  let id1 := idT 1408
  let x2 := compT 1408 tx tx
  enumW capK 128 nWordsK && nWordsK.all (fun w => blkTrivOK blkDataK.blk (tabW w)) &&
    enumW capK 8 zcWordsK && commListsOK (zcWordsK.map tabW) nt && centInOK NL nt ZL &&
    !tblEq 1408 x2 id1 && tblEq 1408 (compT 1408 x2 x2) id1 && !tblEq 1408 ty id1 &&
    tblEq 1408 (compT 1408 ty ty) id1 && !tblEq 1408 ty tx && !tblEq 1408 ty x2 &&
    !tblEq 1408 ty (compT 1408 x2 tx)

@[expose] def tableK3OK : Bool :=
  let qt := qWordsK.map tabW
  let QL := subgroupList capK qWordsK
  let ZL := subgroupList capK zcWordsK
  let EL := subgroupList capK eWordsK
  let id1 := idT 1408
  let tc := tabW cWordK
  enumW capK 32 qWordsK && enumW capK 8 eWordsK && wordOK cWordK && memT 1408 QL tc &&
    memT 1408 ZL tc &&
    !tblEq 1408 tc id1 && tblEq 1408 (compT 1408 tc tc) id1 && centInPairOK QL qt id1 tc &&
    commInOK QL tc && sqInPairOK QL id1 tc && eWordsK.all (fun w => memT 1408 QL (tabW w)) &&
    commListsOK (eWordsK.map tabW) (eWordsK.map tabW) && sqOneOK id1 EL

@[expose] def tableK4OK : Bool :=
  let NL := subgroupList capK nWordsK
  let ZL := subgroupList capK zcWordsK
  let QL := subgroupList capK qWordsK
  let KL := subgroupList capK kWords
  let kt := kWords.map tabW
  prodCoverOK NL ZL QL &&
    centInOK KL kt (pair4 (idT 1408) (tabW wordA) (tabW wordZ) (tabW wordAZ))

@[expose] def tableKOK : Bool := tableK1OK && tableK2OK && tableK3OK && tableK4OK

end CFSG.EvenSporadicStandard.HNRecog
