module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.HNRecog

@[expose] def gen2aConj (h w : List ℕ) : List ℕ := h ++ w ++ h.reverse

@[expose] def gen2aH1 : List ℕ := [3, 1, 3, 1, 1, 1]

@[expose] def gen2aH2 : List ℕ := [1, 1, 3]

@[expose] def gen2aC1 : List ℕ := gen2aConj gen2aH1 wordZ₁

@[expose] def gen2aC2 : List ℕ := gen2aConj gen2aH2 wordB

@[expose] def gen2aG : List ℕ :=
  [7, 5, 1, 7, 4, 1, 5, 6, 1, 2, 3, 1, 3, 5, 7, 5, 6, 5, 7, 3, 1, 2, 1, 6, 5, 1, 6, 1]

@[expose] def gen2aU : List (List ℕ) :=
  classz₁.centGens.map (gen2aConj gen2aH1) ++ classb.centGens.map (gen2aConj gen2aH2)

@[expose] def gen2aTabs : List Table :=
  gen2aU.map tabW ++ (gen2aU.map tabW).map (invT 1408)

@[expose] def gen2aProd : List (ℕ × List ℕ) :=
  [(0, [3, 4, 7, 6, 8, 7, 8, 2, 7, 4, 5, 4, 3, 3, 2, 2, 2, 1, 6, 6, 6, 7, 7, 8, 5, 5]),
    (1, [7, 5, 4, 2, 8, 2, 7, 5, 4, 3, 3, 2, 2, 2, 1, 8, 7, 2, 7, 8, 8, 3, 5, 5]),
    (2, [3, 1, 8, 2, 1, 1, 2, 8, 7, 6, 1, 8, 5, 3, 6, 4, 5, 4, 3, 3, 2, 2, 2, 1, 1]),
    (3, [7, 5, 4, 2, 1, 3, 5, 8, 3, 8, 5, 7, 5, 6, 6, 6, 7, 7, 8, 1, 8, 7, 2, 7, 8, 8, 3, 5, 5, 2,
      5, 5, 2, 2, 5, 5, 2, 5, 5]),
    (4, [8, 7, 8, 1, 6, 6, 3, 3, 4, 3, 6, 8, 3, 5, 2, 4, 3, 1, 4, 5, 5, 2, 5, 5, 2, 2, 5, 5, 2]),
    (5, [2, 4, 2, 2, 7, 6, 1, 8, 1, 6, 4, 1, 2, 8, 7, 5, 4, 5, 5, 7, 4, 5, 7, 5, 5, 4, 3, 3, 2, 2,
      2, 5, 5, 2, 5, 5, 2, 2, 5, 5, 2, 5, 5]),
    (6, [3, 8, 6, 8, 8, 6, 7, 4, 4, 1, 6, 1, 8, 5, 3, 6, 4, 1, 2, 5, 5, 2, 2, 5, 5, 2, 1, 1])]

@[expose] def gen2aBasicOK : Bool :=
  let a := tabW wordA
  let b := tabW wordB
  let c₁ := tabW gen2aC1
  let c₂ := tabW gen2aC2
  let g := tabW gen2aG
  let ab := compT 1408 a b
  gensOK && wordOK wordA && wordOK wordB && wordOK gen2aC1 && wordOK gen2aC2 && wordOK gen2aG &&
    involOK 1408 c₁ && involOK 1408 c₂ && commTT 1408 c₁ b && commTT 1408 c₂ b &&
    !tblEq 1408 c₁ a && !tblEq 1408 c₁ b && !tblEq 1408 c₁ ab && !tblEq 1408 c₂ a &&
    !tblEq 1408 c₂ b && !tblEq 1408 c₂ ab && commTT 1408 g c₁ && commTT 1408 g c₂ &&
    !commTT 1408 g b

@[expose] def gen2aGenOK : Bool :=
  let c₁ := tabW gen2aC1
  let c₂ := tabW gen2aC2
  gensOK && wordOK gen2aC1 && wordOK gen2aC2 && gen2aU.all wordOK &&
    (gen2aU.map tabW).all (fun u => commTT 1408 u c₁ || commTT 1408 u c₂) &&
    (gen2aU.map tabW).all (fun u => invOK 1408 u (invT 1408 u)) && gen2aTabs.all (permOK 1408) &&
    gen2aProd.all fun p => p.2.all (fun l => decide (1 ≤ l ∧ l ≤ 8)) &&
      tblEq 1408 (wordTbl 1408 gen2aTabs p.2) (h1408T p.1)

@[expose] def gen2aOK : Bool := gen2aBasicOK && gen2aGenOK

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
