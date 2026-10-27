module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchFib
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSAutTabData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchNorm

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] def sPc : List ℕ := [3, 68, 4, 69, 512, 4096, 256]

@[expose] def sGens : List ℕ := sPc ++ [128, 34816]

@[expose] def a9LinTab : Array ℕ := Array.ofFn (n := 512) fun v => a9LinLit / 2 ^ (16 * v.val) % 2 ^ 16

@[expose] def a9CoTab : Array ℕ :=
  Array.ofFn (n := 65536) fun c => a9CoRow (c.val / 128) / 2 ^ (9 * (c.val % 128)) % 2 ^ 9

@[expose] def a9K : KCoord := ⟨9, fun v => a9LinTab[v]!, fun c => a9CoTab[c]!⟩

@[expose] def sNfTab : Array (ℕ × ℕ) :=
  Array.ofFn (n := 65536) fun c =>
    (sNfRow (c.val / 128) / 2 ^ (16 * (c.val % 128)) % 2 ^ 7,
      sNfRow (c.val / 128) / 2 ^ (16 * (c.val % 128) + 7) % 2 ^ 9)

@[expose] def sConj (g h : ℕ) : ℕ := cconj sMul sInv g h

@[expose] def sMTab : Array ℕ :=
  Array.ofFn (n := 65536) fun k => sMRow (k.val / 512) / 2 ^ (9 * (k.val % 512)) % 2 ^ 9

@[expose] def sKOrb : Array (List (ℕ × ℕ)) :=
  Array.ofFn (n := 512) fun v => (List.range (sKOrbRow v.val % 2 ^ 8)).map fun k =>
    (sKOrbRow v.val / 2 ^ (32 * k + 8) % 2 ^ 16, sKOrbRow v.val / 2 ^ (32 * k + 24) % 2 ^ 16)

@[expose] def sP : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 64, 128, 256], [1, 2, 4, 8, 16, 32, 64, 128, 257],
    [1, 2, 4, 8, 16, 33, 64, 129, 256], [1, 2, 4, 8, 16, 33, 64, 129, 257],
    [1, 2, 6, 8, 16, 34, 64, 130, 256], [1, 2, 6, 8, 16, 34, 64, 130, 257],
    [1, 2, 6, 8, 16, 35, 64, 131, 256], [1, 2, 6, 8, 16, 35, 64, 131, 257]]

@[expose] def sH : List (List ℕ) :=
  [[3, 68, 4, 69, 512, 4096, 256], [3, 68, 4, 69, 512, 4096, 256],
    [3, 68, 4, 69, 512, 4096, 256], [3, 68, 4, 69, 512, 4096, 256],
    [3, 68, 4, 69, 512, 4160, 256], [3, 68, 4, 69, 512, 4160, 256],
    [3, 68, 4, 69, 512, 4160, 256], [3, 68, 4, 69, 512, 4160, 256]]

@[expose] def sCanon : Array (Array (ℕ × ℕ)) :=
  Array.ofFn (n := 56) fun ki => Array.ofFn (n := 512) fun d =>
    (sCanonRow ((512 * ki.val + d.val) / 128) / 2 ^ (18 * ((512 * ki.val + d.val) % 128)) % 2 ^ 9,
      sCanonRow ((512 * ki.val + d.val) / 128) / 2 ^ (18 * ((512 * ki.val + d.val) % 128) + 9) % 2 ^ 9)

@[expose] def sAutData : AutData where
  K := a9K
  q := 7
  g := fun l => sPc.getD l 0
  nfE := fun x => (sNfTab[x]!).1
  nfA := fun x => (sNfTab[x]!).2
  relE := fun i j => (sNfTab[if j < i then sConj (sPc.getD i 0) (sPc.getD j 0)
    else sMul (sPc.getD i 0) (sPc.getD i 0)]!).1
  relA := fun i j => (sNfTab[if j < i then sConj (sPc.getD i 0) (sPc.getD j 0)
    else sMul (sPc.getD i 0) (sPc.getD i 0)]!).2
  olen := fun v => (sKOrb[v]!).length
  M := fun e v => sMTab[e * 512 + v]!
  cb := fun j i => a9CoTab[sConj (sPc.getD j 0) (a9LinTab[2 ^ i]!)]!
  nk := 8
  P := fun k i => (sP.getD k []).getD i 0
  h := fun k i => (sH.getD k []).getD i 0
  R := fun k i => (List.range 512).filter fun d => ((sCanon[k * 7 + i]!)[d]!).2 == d
  cA := fun k i d => ((sCanon[k * 7 + i]!)[d]!).1
  cD := fun k i d => ((sCanon[k * 7 + i]!)[d]!).2
  gens := sGens

@[expose] def sTree : Array ℕ × Array ℕ × Array ℕ :=
  (Array.ofFn (n := 65536) fun c => sTreeRow (c.val / 128) / 2 ^ (28 * (c.val % 128)) % 2 ^ 16,
    Array.ofFn (n := 65536) fun c => sTreeRow (c.val / 128) / 2 ^ (28 * (c.val % 128) + 16) % 2 ^ 4,
    Array.ofFn (n := 65536) fun c => sTreeRow (c.val / 128) / 2 ^ (28 * (c.val % 128) + 20) % 2 ^ 8)

@[expose] def sAutCheck1 : Bool :=
  invOK sMul sInv 65536 &&
  ((List.range 512).all fun v => decide (a9K.lin v < 65536) && a9K.co (a9K.lin v) == v) &&
  ((List.range 512).all fun v => (List.range 512).all fun w =>
    a9K.lin (v ^^^ w) == sMul (a9K.lin v) (a9K.lin w)) &&
  ((List.range 65536).all fun c =>
    !((List.range 9).all fun j => sMul c (a9K.lin (2 ^ j)) == sMul (a9K.lin (2 ^ j)) c) ||
      (decide (a9K.co c < 2 ^ 9) && a9K.lin (a9K.co c) == c)) &&
  ((List.range 7).all fun l => decide (sAutData.g l < 65536)) &&
  ((List.range 65536).all fun x => decide (sAutData.nfE x < 2 ^ 7) &&
    decide (sAutData.nfA x < 2 ^ 9) &&
    x == sMul (wprodN sMul 7 sAutData.g (sAutData.nfE x)) (a9K.lin (sAutData.nfA x))) &&
  ((List.range 7).all fun i => (List.range (i + 1)).all fun j =>
    decide (sAutData.relA i j < 2 ^ 9) &&
    (if j < i then sConj (sAutData.g i) (sAutData.g j)
      else sMul (sAutData.g i) (sAutData.g i)) ==
      sMul (wprodN sMul i sAutData.g (sAutData.relE i j)) (a9K.lin (sAutData.relA i j))) &&
  (sGens.all fun g => decide (g < 65536)) &&
  treeOK sMul sGens 65536 (fun c => sTree.1[c]!) (fun c => sTree.2.1[c]!) (fun c => sTree.2.2[c]!)

@[expose] def sAutCheck2 : Bool :=
  ((List.range 512).all fun v => orbOK sMul sInv 65536 (a9K.lin v) (sKOrb[v]!) &&
    orbClosed sMul sInv sGens (a9K.lin v) (sKOrb[v]!)) &&
  ((List.range 128).all fun e => (List.range 512).all fun v =>
    decide (sAutData.M e v < 2 ^ 9) &&
    a9K.lin (sAutData.M e v) == sConj (wprodN sMul 7 sAutData.g e) (a9K.lin v)) &&
  ((List.range 7).all fun j => (List.range 9).all fun i =>
    decide (sAutData.cb j i < 2 ^ (i + 1)) &&
    a9K.lin (sAutData.cb j i) == sConj (sAutData.g j) (a9K.lin (2 ^ i))) &&
  ((nSearch 9 7 sAutData.M sAutData.cb sAutData.olen).all fun V =>
    (List.range 8).any fun k => (List.range 128).any fun e =>
      (List.range 9).all fun i => V.getD i 0 == sAutData.M e (sAutData.P k i)) &&
  ((List.range 8).all fun k => (List.range 9).all fun i => decide (sAutData.P k i < 2 ^ 9)) &&
  ((List.range 8).all fun k => (List.range 7).all fun i => decide (sAutData.h k i < 65536))

@[expose] def sAutCheck3 : Bool :=
  ((List.range 8).all fun k => (List.range 7).all fun i => (List.range 512).all fun v =>
    a9K.co (sConj (sAutData.h k i) (a9K.lin (sAutData.Pk k v))) ==
      sAutData.Pk k (a9K.co (sConj (sAutData.g i) (a9K.lin v)))) &&
  ((List.range 8).all fun k => (List.range 7).all fun i =>
    (sAutData.R k i).all fun d => decide (d < 2 ^ 9)) &&
  ((List.range 8).all fun k => (List.range 7).all fun i => (List.range 512).all fun d =>
    decide (sAutData.cA k i d < 2 ^ 9) && (sAutData.R k i).contains (sAutData.cD k i d) &&
    ((List.range i).all fun l => sMul (a9K.lin (sAutData.cA k i d)) (sAutData.h k l) ==
      sMul (sAutData.h k l) (a9K.lin (sAutData.cA k i d))) &&
    sConj (a9K.lin (sAutData.cA k i d)) (sMul (sAutData.h k i) (a9K.lin d)) ==
      sMul (sAutData.h k i) (a9K.lin (sAutData.cD k i d)))

@[expose] def sInvList : List ℕ := (List.range 65536).filter fun c => sMul c c == 0 && c != 0

@[expose] def sInvRec (c : ℕ) : List (ℕ × ℕ) := orbitRec sMul sInv sGens 8 c

@[expose] def sNinv (c : ℕ) : ℕ := (sInvList.filter fun x => sMul x c == sMul c x).length

@[expose] def sY : List ℕ := sInvList.filter fun c =>
  orbClosed sMul sInv sGens c (sInvRec c) && (sInvRec c).length == 8 && sNinv c == 1343

@[expose] def sAutCheck4 : Bool :=
  (sInvList.all fun c => orbOK sMul sInv 65536 c (sInvRec c) &&
    (orbClosed sMul sInv sGens c (sInvRec c) || decide (8 < (sInvRec c).length))) &&
  ((List.range 65536).all fun c =>
    (sY.all fun y => sMul c y == sMul y c) == (decide (a9K.co c < 2 ^ 9) && a9K.lin (a9K.co c) == c))

end CFSG.EvenSmallLie.OmegaEight.SpBranch
