module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Model
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Tabs
public import CFSG.RankThree.Native.PermEnumeration
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer CFSG.F4.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open Matrix

@[expose] def tabOfMat (M : Matrix (Fin 6) (Fin 6) F4) : Array ℕ :=
  let A := Qm * M * Qim
  Array.ofFn (n := 693) fun i => ptIdx (A *ᵥ uVec i.val)

@[expose] def gA (k : ℕ) : Array ℕ := yamTabs[k]!

@[expose] def wA (w : List ℕ) : Array ℕ := w.foldr (fun k acc => compA 693 (gA k) acc) (idA 693)

@[expose] def codesOf (M : Matrix (Fin 6) (Fin 6) F4) : Array ℕ :=
  Array.ofFn (n := 36) fun k => (M ⟨k.val / 6, by omega⟩ ⟨k.val % 6, by omega⟩).code.val

@[expose] def rowC (C : Array ℕ) (v r : ℕ) : ℕ :=
  f4mul C[6 * r]! (coord v 0) ^^^ f4mul C[6 * r + 1]! (coord v 1) ^^^
    f4mul C[6 * r + 2]! (coord v 2) ^^^ f4mul C[6 * r + 3]! (coord v 3) ^^^
    f4mul C[6 * r + 4]! (coord v 4) ^^^ f4mul C[6 * r + 5]! (coord v 5)

@[expose] def mulVecC (C : Array ℕ) (v : ℕ) : ℕ :=
  rowC C v 0 + 4 * rowC C v 1 + 16 * rowC C v 2 + 64 * rowC C v 3 + 256 * rowC C v 4 +
    1024 * rowC C v 5

@[expose] def qmCodes : Array ℕ :=
  #[2, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1, 0,
    0, 3, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 1, 0, 0]

@[expose] def qimCodes : Array ℕ :=
  #[1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1,
    0, 0, 0, 0, 3, 2, 0, 0, 3, 2, 0, 0, 3, 2, 0, 0, 0, 0]

@[expose] def yamCode0 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1]

@[expose] def yamCode1 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 1]

@[expose] def yamCode2 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def yamCode3 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def yamCode4 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def yamCode5 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1]

@[expose] def yamCode6 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 1]

@[expose] def yamCode7 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def yamCode8 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 2, 0, 1, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def yamCode9 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1]

@[expose] def yamCode10 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 1]

@[expose] def yamCode11 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def yamCode12 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1]

@[expose] def yamCode13 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 1]

@[expose] def yamCode14 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1]

@[expose] def yamCode15 : Array ℕ :=
  #[0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]

@[expose] def yamCode16 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def yamCode17 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def yamCodes : Array (Array ℕ) :=
  #[yamCode0, yamCode1, yamCode2, yamCode3, yamCode4, yamCode5, yamCode6, yamCode7, yamCode8,
    yamCode9, yamCode10, yamCode11, yamCode12, yamCode13, yamCode14, yamCode15, yamCode16,
    yamCode17]

@[expose] def tabC (C : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 693) fun i =>
    uPts.toList.idxOf (normC (mulVecC qmCodes (mulVecC C (mulVecC qimCodes uPts[i.val]!))))

@[expose] def tabsCheck : Bool :=
  (List.range 18).all fun k => tabC yamCodes[k]! == gA k && validA 693 (gA k)

structure ChainData where
  gens : List (List ℕ)
  words : List (List ℤ)
  base : List ℕ

namespace ChainData

variable (c : ChainData)

@[expose] def O : Array (Array ℕ) := (c.gens.map wA).toArray

@[expose] def S : Array (Array ℕ) :=
  c.words.foldl (fun S w => S.push (wordA 693 S (rawInvs 693 S) w)) c.O

@[expose] def W : Array (List ℤ) := (List.replicate c.gens.length [] ++ c.words).toArray

@[expose] def B : Array ℕ := c.base.toArray

@[expose] def levels : Array Level := rawLevels 693 c.S c.B

@[expose] def ok : Bool := rawChainOK 693 (c.S.extract 0 c.gens.length) c.S c.B c.W 1

@[expose] def order : ℕ := (rawOrbitSizes 693 c.S c.B).prod

end ChainData

@[expose] def chS : ChainData where
  gens := [[0], [1], [2], [3], [4]]
  words := []
  base := [1, 3, 45]

@[expose] def chX1 : ChainData where
  gens := [[0], [1]]
  words := []
  base := [1]

@[expose] def chX2 : ChainData where
  gens := [[2], [3]]
  words := []
  base := [3]

@[expose] def chX3 : ChainData where
  gens := [[4]]
  words := []
  base := [45]

@[expose] def chK1 : ChainData where
  gens := [[2], [3], [4], [16], [17]]
  words := [[-1, -2, -5, 1, 4, 1], [-6, 3, 6], [-3, -7, 6, 6], [-2, -7, 8, 3, 1]]
  base := [3, 45, 9]

@[expose] def chK2 : ChainData where
  gens := [[0], [1], [2], [3], [15], [16]]
  words := [[-1, 5, 1], [-6, -3, 7, 6], [-3, -8, 4, 8, 3]]
  base := [1, 3, 0]

@[expose] def chA1 : ChainData where
  gens := [[0], [1], [5], [6], [9], [10], [12], [13], [14]]
  words := []
  base := [1]

@[expose] def chA2 : ChainData where
  gens := [[4], [7], [8], [9], [10], [11], [12], [13], [14]]
  words := [[-2, 7], [-6, -10, -9, 4, 1], [-8, 3, 2]]
  base := [45, 3, 1]

@[expose] def chK1A1 : ChainData where
  gens := [[2], [3], [4], [16], [17], [0], [1], [5], [6], [9], [10], [12], [13], [14]]
  words := [[-1, 8], [-15, 3, 15], [-5, -16, -2, 9], [-4, -2, 13, 4], [-15, 18, 15],
    [-16, -19, 17, 19], [-18, 5, 18], [-16, 21, 16]]
  base := [3, 45, 1, 9]

@[expose] def chK2A2 : ChainData where
  gens := [[0], [1], [2], [3], [15], [16], [4], [7], [8], [9], [10], [11], [12], [13], [14]]
  words := [[-6, -3, 9, 6], [-6, -4, 6, 9], [-1, 5, 1], [-6, -3, 18, 6], [-9, -18, 17, 18]]
  base := [1, 3, 45]

@[expose] def chL : ChainData where
  gens := [[0], [1], [2], [3], [4], [15], [16], [17]]
  words := [[-3, -4, -8, 3, 7, 3], [-9, 5, 9], [-5, -10, 9, 9], [-4, -10, 11, 5, 3], [-1, 6, 1],
    [-7, -3, 13, 7], [-5, -10, 14, 9], [-15, 11, 15], [-12, 14, 12], [-17, 10, 17]]
  base := [1, 3, 45, 9, 0]

@[expose] def chB12 : ChainData where
  gens := [[0], [1], [15, 0, 15], [15, 1, 15]]
  words := [[-3, -2, 4, 1]]
  base := [1, 0, 3]

@[expose] def chB23 : ChainData where
  gens := [[2], [3], [16, 2, 16], [16, 3, 16]]
  words := []
  base := [3]

@[expose] def chSJ : ChainData where
  gens := [[0], [1], [2], [3], [4], [15, 1, 15, 0, 1, 15, 1]]
  words := []
  base := [1, 3, 45]

@[expose] def chT1 : ChainData where
  gens := [[2], [3], [4], [7], [8], [11]]
  words := []
  base := [3, 45]

@[expose] def chT2 : ChainData where
  gens := [[0], [1], [2], [3], [5], [6]]
  words := []
  base := [1, 3]

@[expose] def au₁ : Array ℕ := wA [15, 16, 17, 16, 15]

@[expose] def au₂ : Array ℕ := wA [17, 16, 17, 15, 16, 17]

@[expose] def aw₀ : Array ℕ := wA [15, 16, 17, 15, 16, 17, 15, 16, 17]

@[expose] def aj₀ : Array ℕ := wA [15, 1, 15, 0, 1, 15, 1]

@[expose] def aab : Array ℕ := wA [15, 16]

@[expose] def aba : Array ℕ := wA [16, 15]

@[expose] def aaba : Array ℕ := wA [15, 16, 15]

@[expose] def abcb : Array ℕ := wA [16, 17, 16]

@[expose] def lvS : Array Level := chS.levels
@[expose] def lvX1 : Array Level := chX1.levels
@[expose] def lvX2 : Array Level := chX2.levels
@[expose] def lvX3 : Array Level := chX3.levels
@[expose] def lvT1 : Array Level := chT1.levels
@[expose] def lvT2 : Array Level := chT2.levels
@[expose] def lvK1 : Array Level := chK1.levels
@[expose] def lvK2 : Array Level := chK2.levels
@[expose] def lvA1 : Array Level := chA1.levels
@[expose] def lvA2 : Array Level := chA2.levels
@[expose] def lvK1A1 : Array Level := chK1A1.levels
@[expose] def lvK2A2 : Array Level := chK2A2.levels
@[expose] def lvSJ : Array Level := chSJ.levels

@[expose] def eS : ArrCert := enumBfs 693 chS.O chS.base 40000

@[expose] def eT1 : ArrCert := enumBfs 693 chT1.O chT1.base 100

@[expose] def eT2 : ArrCert := enumBfs 693 chT2.O chT2.base 100

@[expose] def eA1 : ArrCert := enumBfs 693 chA1.O chA1.base 1000

@[expose] def eA2 : ArrCert := enumBfs 693 chA2.O chA2.base 1000

@[expose] def eK1 : ArrCert := enumBfs 693 chK1.O chK1.base 30000

@[expose] def validCheck : Bool :=
  validA 693 au₁ && validA 693 au₂ && validA 693 aw₀ && validA 693 aj₀ && validA 693 aab &&
    validA 693 aba && validA 693 aaba && validA 693 abcb && chK1.O.all (validA 693) &&
    chK2.O.all (validA 693)

@[expose] def uNormCheck : Bool :=
  chK1.O.all (fun x => siftA 693 lvK1 chK1.B 0 (conjA 693 au₁ x)) &&
    chK2.O.all (fun x => siftA 693 lvK2 chK2.B 0 (conjA 693 au₂ x))

@[expose] def kNormCheck : Bool :=
  chK1.O.all (fun k => chA1.O.all fun a => siftA 693 lvA1 chA1.B 0 (conjA 693 k a)) &&
    chK2.O.all (fun k => chA2.O.all fun a => siftA 693 lvA2 chA2.B 0 (conjA 693 k a))

@[expose] def sNormCheck : Bool :=
  chS.O.all (fun s => siftA 693 lvS chS.B 0 (conjA 693 aj₀ s)) &&
    (List.range 15).all (fun k => siftA 693 lvS chS.B 0 (gA k))

@[expose] def fixCheck : Bool :=
  chS.O.all (fun s => s[0]! == 0) && allLt 693 (fun p => p == 0 || chS.O.any fun s => s[p]! != p) &&
    chK1A1.O.all (fun s => s[0]! == 0)

@[expose] def sIntCheck : Bool :=
  allLt eS.pts.size fun i =>
    (siftA 693 lvS chS.B 0 (conjA 693 au₂ eS.pts[i]!) == siftA 693 lvT2 chT2.B 0 eS.pts[i]!) &&
    (siftA 693 lvS chS.B 0 (conjA 693 au₁ eS.pts[i]!) == siftA 693 lvT1 chT1.B 0 eS.pts[i]!) &&
    (eqA 693 eS.pts[i]! (idA 693) || !(siftA 693 lvS chS.B 0 (conjA 693 aw₀ eS.pts[i]!)))

@[expose] def t2IntCheck : Bool :=
  allLt eT2.pts.size fun i =>
    (siftA 693 lvT2 chT2.B 0 (conjA 693 aab eT2.pts[i]!) == siftA 693 lvX1 chX1.B 0 eT2.pts[i]!) &&
    (siftA 693 lvT2 chT2.B 0 (conjA 693 aba eT2.pts[i]!) == siftA 693 lvX2 chX2.B 0 eT2.pts[i]!) &&
    (eqA 693 eT2.pts[i]! (idA 693) || !(siftA 693 lvT2 chT2.B 0 (conjA 693 aaba eT2.pts[i]!)))

@[expose] def t1IntCheck : Bool :=
  allLt eT1.pts.size fun i =>
    siftA 693 lvT1 chT1.B 0 (conjA 693 abcb eT1.pts[i]!) == siftA 693 lvX3 chX3.B 0 eT1.pts[i]!

@[expose] def ka1Check : Bool :=
  allLt eA1.pts.size fun i =>
    eqA 693 eA1.pts[i]! (idA 693) || (!(siftA 693 lvK1 chK1.B 0 eA1.pts[i]!) &&
      !(siftA 693 lvK1A1 chK1A1.B 0 (conjA 693 au₁ eA1.pts[i]!)))

@[expose] def ka2Check : Bool :=
  allLt eA2.pts.size fun i =>
    eqA 693 eA2.pts[i]! (idA 693) || (!(siftA 693 lvK2 chK2.B 0 eA2.pts[i]!) &&
      !(siftA 693 lvK2A2 chK2A2.B 0 (conjA 693 au₂ eA2.pts[i]!)))

@[expose] def normCheck : Bool :=
  allLt eK1.pts.size fun i =>
    !(chS.O.all fun s => siftA 693 lvS chS.B 0 (conjA 693 eK1.pts[i]! s)) ||
      siftA 693 lvSJ chSJ.B 0 eK1.pts[i]!

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
