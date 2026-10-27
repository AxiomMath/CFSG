module

public import CFSG.LieType.Chevalley.RootOps.Poly

public section

namespace CFSG.LieType.Steinberg.RankTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps

@[expose] def g2CommPairsOne : List ((ℕ × ℕ) × List Factor) := [
  ((0, 3), [(1, 1, 7, 1)]), ((0, 10), [(1, 1, 6, -1)]), ((1, 8), [(1, 1, 3, 3)]),
  ((1, 9), [(1, 1, 2, 3)]), ((2, 6), [(1, 1, 10, -1)]), ((2, 7), [(1, 1, 3, 1)]),
  ((3, 10), [(1, 1, 2, 1)]), ((4, 5), [(1, 1, 0, 3)]), ((4, 8), [(1, 1, 7, 3)]),
  ((5, 11), [(1, 1, 6, -3)]), ((6, 7), [(1, 1, 0, -1)]), ((9, 11), [(1, 1, 10, -3)])]

@[expose] def g2CommPairsThree : List ((ℕ × ℕ) × List Factor) := [
  ((1, 4), [(1, 1, 8, -2), (1, 2, 7, -3), (2, 1, 3, -3)]),
  ((1, 11), [(1, 1, 9, 2), (1, 2, 10, 3), (2, 1, 2, 3)]),
  ((4, 11), [(1, 1, 5, -2), (1, 2, 6, -3), (2, 1, 0, -3)]),
  ((5, 8), [(1, 1, 4, -2), (1, 2, 7, 3), (2, 1, 0, 3)]),
  ((5, 9), [(1, 1, 11, 2), (1, 2, 10, -3), (2, 1, 6, -3)]),
  ((8, 9), [(1, 1, 1, -2), (1, 2, 2, 3), (2, 1, 3, 3)])]

@[expose] def g2CommPairsFour : List ((ℕ × ℕ) × List Factor) := [
  ((0, 1), [(1, 1, 4, 1), (1, 2, 8, -1), (1, 3, 3, -1), (2, 3, 7, 1)]),
  ((0, 9), [(1, 1, 5, -1), (1, 2, 11, 1), (1, 3, 10, -1), (2, 3, 6, -1)]),
  ((1, 6), [(1, 1, 11, -1), (2, 1, 9, -1), (3, 1, 2, -1), (3, 2, 10, -2)]),
  ((2, 4), [(1, 1, 1, 1), (1, 2, 8, 1), (1, 3, 7, 1), (2, 3, 3, -1)]),
  ((2, 5), [(1, 1, 9, -1), (1, 2, 11, -1), (1, 3, 6, 1), (2, 3, 10, 1)]),
  ((3, 5), [(1, 1, 8, -1), (1, 2, 4, 1), (1, 3, 0, -1), (2, 3, 7, -1)]),
  ((3, 11), [(1, 1, 1, 1), (1, 2, 9, -1), (1, 3, 10, -1), (2, 3, 2, 1)]),
  ((4, 10), [(1, 1, 11, -1), (2, 1, 5, 1), (3, 1, 0, 1), (3, 2, 6, 2)]),
  ((6, 8), [(1, 1, 5, -1), (1, 2, 4, -1), (1, 3, 7, 1), (2, 3, 0, 1)]),
  ((7, 9), [(1, 1, 8, -1), (1, 2, 1, -1), (1, 3, 2, 1), (2, 3, 3, 1)]),
  ((7, 11), [(1, 1, 4, 1), (1, 2, 5, 1), (1, 3, 6, 1), (2, 3, 0, -1)]),
  ((8, 10), [(1, 1, 9, 1), (2, 1, 1, -1), (3, 1, 3, 1), (3, 2, 2, -2)])]

@[expose] def g2CommPairs : List ((ℕ × ℕ) × List Factor) :=
  g2CommPairsOne ++ g2CommPairsThree ++ g2CommPairsFour

@[expose] def g2CommInv (fs : List Factor) : List Factor :=
  fs.reverse.map fun f => (f.2.1, f.1, f.2.2.1, -f.2.2.2)

@[expose] def g2CommCheckRange (lo k : ℕ) : Bool :=
  (List.range' lo k).all fun n =>
    match g2CommPairs[n]? with
    | some e => repCheck .G2 e.1.1 e.1.2 e.2
    | none => true

@[expose] def g2CommLookup (T : List ((ℕ × ℕ) × List Factor)) (a b : ℕ) : List Factor :=
  match T.find? (fun e => e.1 == (a, b)) with
  | some e => e.2
  | none =>
    match T.find? (fun e => e.1 == (b, a)) with
    | some e => g2CommInv e.2
    | none => []

@[expose] def g2CommFactors (a b : ℕ) : List Factor := g2CommLookup g2CommPairs a b


@[expose] def g2CommExps (fs : List Factor) : List (ℕ × ℕ) := fs.map fun f => (f.1, f.2.1)

@[expose] def g2CommCoeff (fs : List Factor) (p : ℕ × ℕ) : ℤ :=
  match fs.find? (fun f => (f.1, f.2.1) == p) with
  | some f => f.2.2.2
  | none => 1

abbrev g2CommRoot (g : ℕ) : Fin (Tag.rank .G2) → ℤ := (Tag.rootCertificate .G2).root g

@[expose] def g2CommCommutes (g g' : ℕ) : Bool :=
  g == g' || (!CFSG.LieType.Ree.vecBEq (g2CommRoot g + g2CommRoot g') 0 &&
    (g2CommFactors g g').isEmpty)

@[expose] def g2CommSwapOf : List Factor → List Factor
  | [fA, fB, fZ, fW] =>
    [fB, fA, fZ, (fW.1, fW.2.1, fW.2.2.1, fW.2.2.2 +
      g2CommCoeff (g2CommFactors fA.2.2.1 fB.2.2.1) (1, 1) * fA.2.2.2 * fB.2.2.2)]
  | fs => fs

@[expose] def g2CommDeriveOk : List Factor → Bool
  | [fA, fB, fZ, fW] =>
    Nat.blt fA.2.2.1 12 && Nat.blt fB.2.2.1 12 && Nat.blt fZ.2.2.1 12 && Nat.blt fW.2.2.1 12 &&
      fA.2.2.1 != fB.2.2.1 &&
      !CFSG.LieType.Ree.vecBEq (g2CommRoot fA.2.2.1 + g2CommRoot fB.2.2.1) 0 &&
      g2CommFactors fA.2.2.1 fB.2.2.1 ==
        [(1, 1, fW.2.2.1, g2CommCoeff (g2CommFactors fA.2.2.1 fB.2.2.1) (1, 1))] &&
      fW.1 == fA.1 + fB.1 && fW.2.1 == fA.2.1 + fB.2.1 &&
      g2CommCommutes fW.2.2.1 fA.2.2.1 && g2CommCommutes fW.2.2.1 fB.2.2.1 &&
      g2CommCommutes fW.2.2.1 fZ.2.2.1
  | _ => true

@[expose] def g2CommSwaps : List ((ℕ × ℕ) × List Factor) :=
  g2CommPairs.map fun e => (e.1, g2CommSwapOf e.2)

@[expose] def g2CommSwapFactors (a b : ℕ) : List Factor := g2CommLookup g2CommSwaps a b

@[expose] def g2CommDet (a b : ℕ) : ℤ :=
  g2CommRoot a ⟨0, by decide⟩ * g2CommRoot b ⟨1, by decide⟩ -
    g2CommRoot a ⟨1, by decide⟩ * g2CommRoot b ⟨0, by decide⟩

@[expose] def g2CommCramer (a b g : ℕ) : ℕ × ℕ :=
  (((g2CommRoot g ⟨0, by decide⟩ * g2CommRoot b ⟨1, by decide⟩ -
      g2CommRoot g ⟨1, by decide⟩ * g2CommRoot b ⟨0, by decide⟩) / g2CommDet a b).toNat,
    ((g2CommRoot a ⟨0, by decide⟩ * g2CommRoot g ⟨1, by decide⟩ -
      g2CommRoot a ⟨1, by decide⟩ * g2CommRoot g ⟨0, by decide⟩) / g2CommDet a b).toNat)

@[expose] def g2CommComplete (a b : ℕ) (E : List (ℕ × ℕ)) : Bool :=
  (List.range (Tag.rootCertificate .G2).roots.length).all fun g =>
    !(Nat.blt 0 (g2CommCramer a b g).1 && Nat.blt 0 (g2CommCramer a b g).2 &&
      CFSG.LieType.Ree.vecBEq (g2CommRoot g)
        ((g2CommCramer a b g).1 • g2CommRoot a + (g2CommCramer a b g).2 • g2CommRoot b)) ||
      E.contains (g2CommCramer a b g)

@[expose] def g2CommNonCentral (a b : ℕ) (p : ℕ × ℕ) : Bool :=
  (g2CommFactors a b).length == 4 && Nat.ble (p.1 + p.2) 3

@[expose] def g2CommCommute (a b : ℕ) (fs : List Factor) : Bool :=
  fs.all fun f => g2CommNonCentral a b (f.1, f.2.1) || fs.all fun f' =>
    g2CommCommutes f.2.2.1 f'.2.2.1

@[expose] def g2CommNatAbs (fs : List Factor) : Bool :=
  fs.all fun f => f.2.2.2.natAbs == 1 || f.2.2.2.natAbs == 2 || f.2.2.2.natAbs == 3

@[expose] def g2CommListOk (a b : ℕ) (fs : List Factor) : Bool :=
  fs.all (coneOk .G2 a b) && g2CommComplete a b (g2CommExps fs) &&
    decide (g2CommExps fs).Nodup && g2CommCommute a b fs

@[expose] def g2CommSwapOk (a b : ℕ) : Bool :=
  (g2CommFactors a b).length != 4 ||
    (g2CommListOk a b (g2CommSwapFactors a b) &&
      ((g2CommExps (g2CommFactors a b)).filter (g2CommNonCentral a b)).length == 2 &&
      (g2CommExps (g2CommSwapFactors a b)).filter (g2CommNonCentral a b) ==
        ((g2CommExps (g2CommFactors a b)).filter (g2CommNonCentral a b)).reverse)

@[expose] def g2CommPairOk (a b : ℕ) : Bool :=
  a == b || CFSG.LieType.Ree.vecBEq (g2CommRoot a + g2CommRoot b) 0 ||
    (g2CommDet a b != 0 && g2CommListOk a b (g2CommFactors a b) && g2CommSwapOk a b)

@[expose] def g2CommAllOk : Bool :=
  g2CommPairs.all (fun e => g2CommDeriveOk e.2) &&
    (List.range 12).all fun a => (List.range 12).all fun b =>
      g2CommPairOk a b && g2CommNatAbs (g2CommFactors a b) && g2CommNatAbs (g2CommSwapFactors a b)

@[expose] def g2CommChoose (L : List (ℕ × ℕ)) (a b : ℕ) : List Factor :=
  if L.filter (g2CommNonCentral a b) =
      (g2CommExps (g2CommFactors a b)).filter (g2CommNonCentral a b) then
    g2CommFactors a b
  else g2CommSwapFactors a b

end CFSG.LieType.Steinberg.RankTwo
