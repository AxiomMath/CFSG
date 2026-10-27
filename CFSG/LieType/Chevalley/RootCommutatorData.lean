module

public import CFSG.LieType.Chevalley.RootCommutatorPairs
public import CFSG.LieType.Chevalley.RootOps.Comm
public import CFSG.Blueprint.ChevalleyPinned

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

@[expose] def isRootB (τ : Tag) (v : Fin τ.rank → ℤ) : Bool :=
  (List.range τ.rootCertificate.roots.length).any fun k =>
    CFSG.LieType.Ree.vecBEq (τ.rootCertificate.root k) v

@[expose] def combAt (τ : Tag) (x y : ℕ) (p : ℕ × ℕ) : Fin τ.rank → ℤ :=
  p.1 • τ.rootCertificate.root x + p.2 • τ.rootCertificate.root y

@[expose] def commPairsAt (τ : Tag) (x y : ℕ) : List (ℕ × ℕ) :=
  commCandidates.filter fun p => isRootB τ (combAt τ x y p)

@[expose] def boxCheck (τ : Tag) (x y : ℕ) : Bool :=
  (List.range' 1 7).all fun a => (List.range' 1 7).all fun b =>
    (Nat.ble a 3 && Nat.ble b 3) || !isRootB τ (combAt τ x y (a, b))

@[expose] def repShapeCheck (τ : Tag) (M : ℕ) (r : ℕ × ℕ × List Factor) : Bool :=
  Nat.blt r.1 τ.rank && decide (0 < height (τ.rootCertificate.root r.2.1)) &&
    r.2.2.map (fun f => (f.1, f.2.1)) == commPairsAt τ r.1 r.2.1 && boxCheck τ r.1 r.2.1 &&
    r.2.2.all fun f => Nat.ble 1 f.2.2.2.natAbs && Nat.ble f.2.2.2.natAbs M

@[expose] def commConstBound : Tag → ℕ
  | .G2 => 3
  | .F4 => 3
  | .D4 => 1
  | .E6 => 1
  | .E7 => 1
  | .E8 => 1

@[expose] def simplyLacedCheck (τ : Tag) : Bool :=
  (repsOf τ).all fun r => r.2.2.all fun f => f.1 == 1 && f.2.1 == 1

@[expose] def longestWord : Tag → List ℕ
  | .G2 => [0, 1, 0, 1, 0, 1]
  | .F4 => [0, 1, 0, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3]
  | .D4 => [0, 1, 2, 0, 1, 2, 3, 2, 0, 1, 2, 3]
  | .E6 => [0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2,
      4, 3, 1, 5, 4, 3, 2, 0]
  | .E7 => [0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2,
      4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2,
      3, 4, 5, 6]
  | .E8 => [0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2,
      4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2,
      3, 4, 5, 6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5,
      6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7]

@[expose] def longestCheck
    (τ : Tag) : Bool :=
  (List.finRange τ.rank).all fun j => (List.finRange τ.rank).any fun k =>
    (walkPair τ ((longestWord τ).map τ.idx) ((j : ℕ), (j : ℕ))).1 ==
      τ.rootCertificate.image k k

end CFSG.LieType.Chevalley.RootOps
