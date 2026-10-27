module

public import CFSG.GF2Type.Smith1979.GammaU.SigmaInputs

public section

namespace CFSG.GF2Type.Smith1979.GammaU.SigmaP

open CFSG.GF2Type.Smith1979.GammaU

@[expose] def combo : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: L, m => (if m % 2 = 1 then a else 0) ^^^ combo L (m / 2)

@[expose] def six (L : List ℕ) : List ℕ := L ++ L.map theta0N

@[expose] def kBasis (i : ℕ) : List ℕ := if i = 0 then [12, 48, 51] else [5, 48, 136]

@[expose] def coordOf (B : List ℕ) (x : ℕ) : ℕ :=
  ((List.range 64).find? fun m => combo B m == x).getD 64

@[expose] def kCS (B6 S : List ℕ) : List (ℕ × ℕ) := S.map fun x => (x, coordOf B6 x)

@[expose] def kTripleOK (B6 S : List ℕ) (CS : List (ℕ × ℕ)) (b u : List ℕ) : Bool :=
  !(CS.all (fun p => S.contains (combo (six u) p.2)) &&
      (List.range 63).all (fun m => combo (six u) (m + 1) != combo B6 (m + 1)) &&
      (b.zip u).all fun p =>
        combo (six u) (coordOf B6 (combo (six u) (coordOf B6 p.2))) == p.1) ||
    u == b.map theta0N || u == b.map fun x => theta0N (theta0N x)

@[noinline, expose] def kTriples (B6 S : List ℕ) (CS : List (ℕ × ℕ)) (b : List ℕ) : Bool :=
  S.all fun u₁ => S.all fun u₂ => S.all fun u₃ => kTripleOK B6 S CS b [u₁, u₂, u₃]

@[noinline, expose] def kHead (b B6 S : List ℕ) (CS : List (ℕ × ℕ)) (SB SP : List ℕ) : Bool :=
  b.all S.contains && (List.range 63).all (fun m => combo B6 (m + 1) != 0) &&
    CS.all (fun p => combo B6 p.2 == p.1) &&
    (List.range 4096).all fun v => SB.any (f0b v) || SP.contains v

@[expose] def kCheckAt (i : ℕ) : Bool :=
  kHead (kBasis i) (six (kBasis i)) (s45 i) (kCS (six (kBasis i)) (s45 i)) (sigmaBasis i)
      (spanList (sigmaBasis i)) &&
    kTriples (six (kBasis i)) (s45 i) (kCS (six (kBasis i)) (s45 i)) (kBasis i)

@[expose] def kCheck (_ : Unit := ()) : Bool := kCheckAt 0 && kCheckAt 1

end CFSG.GF2Type.Smith1979.GammaU.SigmaP
