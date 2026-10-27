module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagPlaneBits

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree

@[expose] def rfCartanL : List (List ℤ) :=
  [[2, 0, -1, 0, 0, 0], [0, 2, 0, -1, 0, 0], [-1, 0, 2, -1, 0, 0], [0, -1, -1, 2, -1, 0],
    [0, 0, 0, -1, 2, -1], [0, 0, 0, 0, -1, 2]]

@[expose] def rfCartanMod3 : List (List ℕ) :=
  [[2, 0, 2, 0, 0, 0], [0, 2, 0, 2, 0, 0], [2, 0, 2, 2, 0, 0], [0, 2, 2, 2, 2, 0],
    [0, 0, 0, 2, 2, 2], [0, 0, 0, 0, 2, 2]]

@[expose] def rfAdjN : List (List ℕ) :=
  [[4, 3, 5, 6, 4, 2], [3, 6, 6, 9, 6, 3], [5, 6, 10, 12, 8, 4], [6, 9, 12, 18, 12, 6],
    [4, 6, 8, 12, 10, 5], [2, 3, 4, 6, 5, 4]]

@[expose] def rfLamN : List ℕ := [4, 3, 5, 6, 4, 2]

@[expose] def rfDotL : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a * b + rfDotL as bs
  | _, _ => 0

@[expose] def rfDotN : List ℕ → List ℕ → ℕ
  | a :: as, b :: bs => a * b + rfDotN as bs
  | _, _ => 0

@[expose] def rfRes3 (x : ℤ) : ℕ := (x % 3).toNat

@[expose] def rfIform (a b : List ℤ) : ℤ := rfDotL a (rfCartanL.map fun row => rfDotL row b)

@[expose] def rfPlaneVecs (k₁ k₂ : List ℕ) : List (List ℕ) :=
  (List.range 3).flatMap fun a => (List.range 3).map fun b => comb a b k₁ k₂

@[expose] def rfRoots : List (List ℤ × List ℕ) := e6ArtifactRoots.map fun r => (r, r.map rfRes3)

@[expose] def rfCands (k₁ k₂ : List ℕ) (j : ℕ) : List (List ℤ × List ℤ) :=
  ((rfRoots.filter fun p =>
    rfDotN p.2 k₁ % 3 == k₁.getD j 0 % 3 && rfDotN p.2 k₂ % 3 == k₂.getD j 0 % 3).map Prod.fst).map
      fun r => (r, rfCartanL.map fun row => rfDotL row r)

@[expose] def rfGramOK (sel : List (List ℤ)) (c : List ℤ × List ℤ) : Bool :=
  let col := rfCartanL.map fun row => row.getD sel.length 0
  (sel.zip col).all fun p => rfDotL p.1 c.2 == p.2

@[expose] def rfLeaves (cs : List (List (List ℤ × List ℤ))) :
    ℕ → List (List ℤ) → List (List (List ℤ))
  | 0, sel => [sel]
  | n + 1, sel =>
    ((cs.getD sel.length []).filter (rfGramOK sel)).flatMap fun c =>
      rfLeaves cs n (sel ++ [c.1])

@[expose] def rfMt (l : List ℤ) (β : List (List ℤ)) : List ℤ := β.map fun b => rfDotL l b

@[expose] def rfUnit (j : ℕ) : List ℤ := (List.range 6).map fun i => if i == j then 1 else 0

@[expose] def rfHasFix (β : List (List ℤ)) : Bool :=
  (List.range 6).any fun j =>
    let e := rfUnit j
    let l1 := rfMt e β
    let l2 := rfMt l1 β
    let N := List.zipWith (· + ·) e (List.zipWith (· + ·) l1 l2)
    N != List.replicate 6 0 && rfMt N β == N

@[expose] def rfModEq3 (u v : List ℕ) : Bool :=
  (List.zipWith (fun x y => x % 3 == y % 3) u v).all id

@[expose] def rfLincomb3 (m : List ℕ) (β3 : List (List ℕ)) : List ℕ :=
  (List.range 6).map fun i => rfDotN m (β3.map fun b => b.getD i 0) % 3

@[expose] def rfCCond (β3 : List (List ℕ)) : Bool := rfModEq3 (rfLincomb3 rfLamN β3) rfLamN

@[expose] def rfMOf (κ : List ℕ) : List ℕ := (rfAdjN.map fun row => rfDotN row κ).map (· / 3)

@[expose] def rfCls0 (β3 : List (List ℕ)) (κs : List (List ℕ)) : Bool :=
  κs.all fun κ =>
    let m := rfMOf κ
    rfModEq3 (rfCartanMod3.map fun row => rfDotN row m) κ && rfModEq3 (rfLincomb3 m β3) m

@[expose] def rfLeafOK (k₁ k₂ : List ℕ) (β : List (List ℤ)) : Bool :=
  let β3 := β.map (·.map rfRes3)
  !(rfCCond β3) || rfCls0 β3 (rfPlaneVecs k₁ k₂) || rfHasFix β

@[expose] def rfPlaneCheck (k₁ k₂ : List ℕ) : Bool :=
  (rfLeaves ((List.range 6).map (rfCands k₁ k₂)) 6 []).all (rfLeafOK k₁ k₂)

@[expose] def rfPlaneBases : List (List ℕ × List ℕ) :=
  [([0, 0, 0, 1, 0, 0], [1, 1, 1, 0, 1, 1]), ([0, 0, 0, 1, 0, 0], [1, 1, 1, 0, 2, 2]),
    ([0, 0, 0, 1, 0, 0], [1, 2, 1, 0, 1, 1]), ([0, 0, 0, 1, 0, 0], [1, 2, 1, 0, 2, 2]),
    ([0, 0, 1, 0, 1, 0], [1, 1, 0, 1, 0, 1]), ([0, 0, 1, 0, 1, 0], [1, 1, 0, 1, 1, 2]),
    ([0, 0, 1, 0, 1, 0], [1, 2, 0, 2, 0, 1]), ([0, 0, 1, 0, 1, 0], [1, 2, 0, 2, 1, 2]),
    ([0, 0, 1, 1, 0, 2], [1, 1, 0, 1, 1, 2]), ([0, 0, 1, 1, 0, 2], [1, 1, 0, 2, 2, 0]),
    ([0, 0, 1, 1, 0, 2], [1, 2, 0, 0, 2, 0]), ([0, 0, 1, 1, 0, 2], [1, 2, 0, 2, 1, 2]),
    ([0, 0, 1, 1, 2, 1], [1, 1, 0, 1, 0, 1]), ([0, 0, 1, 1, 2, 1], [1, 1, 0, 2, 2, 0]),
    ([0, 0, 1, 1, 2, 1], [1, 2, 0, 0, 2, 0]), ([0, 0, 1, 1, 2, 1], [1, 2, 0, 2, 0, 1]),
    ([0, 1, 1, 0, 0, 2], [1, 0, 0, 1, 1, 2]), ([0, 1, 1, 0, 0, 2], [1, 0, 0, 2, 2, 0]),
    ([0, 1, 1, 0, 0, 2], [1, 0, 2, 1, 1, 0]), ([0, 1, 1, 0, 0, 2], [1, 0, 2, 2, 2, 1]),
    ([0, 1, 1, 0, 2, 1], [1, 0, 0, 1, 0, 1]), ([0, 1, 1, 0, 2, 1], [1, 0, 0, 2, 2, 0]),
    ([0, 1, 1, 0, 2, 1], [1, 0, 2, 1, 1, 0]), ([0, 1, 1, 0, 2, 1], [1, 0, 2, 2, 0, 2]),
    ([0, 1, 1, 2, 1, 0], [1, 0, 0, 1, 0, 1]), ([0, 1, 1, 2, 1, 0], [1, 0, 0, 1, 1, 2]),
    ([0, 1, 1, 2, 1, 0], [1, 0, 2, 2, 0, 2]), ([0, 1, 1, 2, 1, 0], [1, 0, 2, 2, 2, 1]),
    ([0, 1, 2, 0, 2, 0], [1, 0, 0, 1, 0, 1]), ([0, 1, 2, 0, 2, 0], [1, 0, 0, 1, 1, 2]),
    ([0, 1, 2, 0, 2, 0], [1, 0, 2, 2, 0, 2]), ([0, 1, 2, 0, 2, 0], [1, 0, 2, 2, 2, 1]),
    ([0, 1, 2, 2, 0, 1], [1, 0, 0, 1, 1, 2]), ([0, 1, 2, 2, 0, 1], [1, 0, 0, 2, 2, 0]),
    ([0, 1, 2, 2, 0, 1], [1, 0, 2, 1, 1, 0]), ([0, 1, 2, 2, 0, 1], [1, 0, 2, 2, 2, 1]),
    ([0, 1, 2, 2, 1, 2], [1, 0, 0, 1, 0, 1]), ([0, 1, 2, 2, 1, 2], [1, 0, 0, 2, 2, 0]),
    ([0, 1, 2, 2, 1, 2], [1, 0, 2, 1, 1, 0]), ([0, 1, 2, 2, 1, 2], [1, 0, 2, 2, 0, 2])]

theorem rfPlanes_true : rfPlaneBases.all (fun p => rfPlaneCheck p.1 p.2) = true := by
  decide +kernel

@[expose] def rfPlaneSets : List ℕ := rfPlaneBases.map fun p => planeBits p.1 p.2

@[expose] def rfIdxVecs : List (ℕ × List ℕ) := (allVecs 6).map fun v => (vecIdx v, v)

@[expose] def rfCovSet (j : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | H :: rest, acc => rfCovSet j rest (if Nat.testBit H j then acc ||| H else acc)

@[expose] def rfCover (Hs planes : List ℕ) : Bool :=
  rfIdxVecs.all fun p₁ =>
    let U := rfCovSet p₁.1 Hs 0
    U == 2 ^ (3 ^ 6) - 1 ||
      rfIdxVecs.all fun p₂ => Nat.testBit U p₂.1 || planes.contains (planeBits p₁.2 p₂.2)

theorem rfCover_true :
    rfCover ((posRoots e6ArtifactRoots).map hyperBits) rfPlaneSets = true := by
  decide +kernel

end CFSG.LieType.SeitzGeneration.ExcWideThree
