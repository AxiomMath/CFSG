module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCheck

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.HNRecog

@[expose] def witSylow : List (List ℕ) :=
  [[7], [2, 5, 7, 2, 7, 1, 2, 3, 7, 5, 6, 5, 7, 3, 1, 5, 1, 6],
    [4, 7, 4, 3, 7, 6, 2, 6, 7, 2, 7, 2, 3],
    [5, 7, 6, 7, 2, 6, 3, 7, 2, 7, 1, 5, 6, 1, 2, 1, 5, 1, 6],
    [1, 2, 7, 5, 7, 6, 3, 5, 6, 3, 6, 1, 2, 1]]

@[expose] def witConjB : List (List ℕ) :=
  [[2, 5, 1, 6, 3], [1, 5, 7, 4, 7, 2], [5, 6, 3, 6], [2, 3, 3, 3, 5, 4], [3, 5, 3, 4, 6, 2, 2],
    [6, 3, 5, 2]]

@[expose] def witConjAZ : List (List ℕ) :=
  [[5, 7, 4, 7, 2, 3], [6, 5, 4], [1, 6, 1, 2, 5, 6], [6, 4, 1, 3, 2, 1, 5], [6, 3, 5, 7, 2, 5],
    [4, 6, 5, 1, 7, 4], [3, 4, 5, 7, 5, 1, 2], [4, 7, 6, 5, 7, 3], [4, 3, 2, 5, 4, 5, 1],
    [1, 2, 3, 5]]

@[expose] def witV : List Table :=
  witConjB.map (fun h => conjTab h (tabW wordB)) ++
    witConjAZ.map (fun h => conjTab h (tabW wordAZ))

@[expose] def conjOK (h : List ℕ) : Bool :=
  wordOK h && invOK 1408 (tabW h) (invT 1408 (tabW h))

@[expose, noinline] def vertGood (a b : Table) (Laz Lb : Array Table) (v : Table) : Bool :=
  let p := compT 1408 b v
  let s := powT 1408 2 p
  !commTT 1408 v b && !ordTest 1408 5 p &&
    (!ordTest 1408 4 p || tblEq 1408 s a || memT 1408 Laz s || memT 1408 Lb s)

@[expose, noinline] def vertsOK (a b : Table) (Laz Lb : Array Table) (V : List Table) : Bool :=
  V.all (vertGood a b Laz Lb)

@[expose, noinline] def vertCoverOK (a b : Table) (V : List Table) (S : Array Table) : Bool :=
  let ab := compT 1408 a b
  S.all fun s => !involOK 1408 s || tblEq 1408 s a || tblEq 1408 s b || tblEq 1408 s ab ||
    V.any fun v => commTT 1408 v s

@[expose] def witOK : Bool :=
  let a := tabW wordA
  let b := tabW wordB
  let Laz := classList invCap classaz.rep
  let Lb := classList invCap classb.rep
  gensOK && enumW invCap 256 witSylow && witSylow.all wordOK && commWordsOK witSylow b &&
    witConjB.all conjOK && witConjAZ.all conjOK && wordOK wordA && wordOK wordAZ &&
    vertsOK a b Laz Lb witV && vertCoverOK a b witV (subgroupList invCap witSylow)

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
