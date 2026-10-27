module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicCertInputs

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def enc : List ℕ → ℕ
  | [] => 0
  | a :: l => a + 64 * enc l

@[expose] def pg (c i : ℕ) : ℕ := Nat.land (Nat.shiftRight c (Nat.mul 6 i)) 63

@[expose] def pcomp (c d : ℕ) : ℕ :=
  Nat.add (pg c (pg d 0)) (Nat.mul 64 (Nat.add (pg c (pg d 1)) (Nat.mul 64 (
    Nat.add (pg c (pg d 2)) (Nat.mul 64 (Nat.add (pg c (pg d 3)) (Nat.mul 64 (
    Nat.add (pg c (pg d 4)) (Nat.mul 64 (Nat.add (pg c (pg d 5)) (Nat.mul 64 (
    Nat.add (pg c (pg d 6)) (Nat.mul 64 (Nat.add (pg c (pg d 7)) (Nat.mul 64 (
    Nat.add (pg c (pg d 8)) (Nat.mul 64 (Nat.add (pg c (pg d 9)) (Nat.mul 64 (
    Nat.add (pg c (pg d 10)) (Nat.mul 64 (Nat.add (pg c (pg d 11)) (Nat.mul 64 (
    Nat.add (pg c (pg d 12)) (Nat.mul 64 (Nat.add (pg c (pg d 13)) (Nat.mul 64 (
    Nat.add (pg c (pg d 14)) (Nat.mul 64 (Nat.add (pg c (pg d 15)) (Nat.mul 64 (
    Nat.add (pg c (pg d 16)) (Nat.mul 64 (Nat.add (pg c (pg d 17)) (Nat.mul 64 (
    Nat.add (pg c (pg d 18)) (Nat.mul 64 (Nat.add (pg c (pg d 19)) (Nat.mul 64 (
    Nat.add (pg c (pg d 20)) (Nat.mul 64 (Nat.add (pg c (pg d 21)) (Nat.mul 64 (
    Nat.add (pg c (pg d 22)) (Nat.mul 64 (Nat.add (pg c (pg d 23)) (Nat.mul 64 (
    Nat.add (pg c (pg d 24)) (Nat.mul 64 (Nat.add (pg c (pg d 25)) (Nat.mul 64 (
    Nat.add (pg c (pg d 26)) (Nat.mul 64 (Nat.add (pg c (pg d 27)) (Nat.mul 64 (
    Nat.add (pg c (pg d 28)) (Nat.mul 64 (Nat.add (pg c (pg d 29)) (Nat.mul 64 (
    Nat.add (pg c (pg d 30)) (Nat.mul 64 (Nat.add (pg c (pg d 31)) (Nat.mul 64 (
    Nat.add (pg c (pg d 32)) (Nat.mul 64 (Nat.add (pg c (pg d 33)) (Nat.mul 64 (
    Nat.add (pg c (pg d 34)) (Nat.mul 64 (Nat.add (pg c (pg d 35)) (Nat.mul 64 (
    Nat.add (pg c (pg d 36)) (Nat.mul 64 (Nat.add (pg c (pg d 37)) (Nat.mul 64 (
    Nat.add (pg c (pg d 38)) (Nat.mul 64 (Nat.add (pg c (pg d 39)) (Nat.mul 64 (
    Nat.add (pg c (pg d 40)) (Nat.mul 64 (Nat.add (pg c (pg d 41)) (Nat.mul 64 (
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

@[expose] def pid : ℕ := enc (List.range 42)

@[expose] def isId (c : ℕ) : Bool := Nat.beq c pid

@[expose] def psq (c : ℕ) : ℕ := pcomp c c

@[expose] def pcube (c : ℕ) : ℕ := pcomp c (psq c)

@[expose] def commC (c d : ℕ) : Bool := Nat.beq (pcomp c d) (pcomp d c)

@[expose] def memB (x : ℕ) : List ℕ → Bool
  | [] => false
  | a :: l => Nat.beq x a || memB x l

@[expose] def nodupB : List ℕ → Bool
  | [] => true
  | a :: l => !(memB a l) && nodupB l

@[expose] def tcode (t : Tab) : ℕ := enc t.toList

@[expose] def gcode (j : ℕ) : ℕ := tcode (genT j)

@[expose] def wcode (w : List ℕ) : ℕ := w.foldl (fun c j => pcomp c (gcode j)) pid

@[expose] def t0g : List ℕ := wT₀.map wcode

@[expose] def t0W : List (List ℕ) :=
    [[], [0], [1], [2], [3], [0, 0], [0, 1], [0, 2], [0, 3], [1, 0], [1, 2], [1, 3], [2, 0],
     [2, 3], [3, 0], [3, 1], [3, 2], [0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 0, 3], [0, 1, 0],
     [0, 1, 2], [0, 1, 3], [0, 2, 3], [0, 3, 0], [0, 3, 1], [0, 3, 2], [1, 0, 1], [1, 0, 2],
     [1, 0, 3], [1, 2, 0], [1, 2, 3], [1, 3, 2], [2, 0, 1], [2, 0, 3], [2, 3, 0], [2, 3, 1],
     [2, 3, 2], [3, 0, 1], [3, 1, 2], [3, 2, 3], [0, 0, 0, 1], [0, 0, 0, 3], [0, 0, 1, 0],
     [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 2, 3], [0, 0, 3, 0], [0, 0, 3, 1], [0, 0, 3, 2],
     [0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 2, 0], [0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 3, 1],
     [0, 3, 1, 2], [0, 3, 2, 3], [1, 2, 0, 1], [2, 3, 2, 3], [0, 0, 0, 1, 0], [0, 0, 1, 0, 1],
     [0, 0, 3, 2, 3]]

@[expose] def t0code (w : List ℕ) : ℕ := w.foldl (fun c j => pcomp c (t0g.getD j pid)) pid

@[expose] def t0L : List ℕ := t0W.map t0code

@[expose] def r2c : ℕ := tcode r₂T

@[expose] def r3c : ℕ := tcode r₃T

@[expose] def r4c : ℕ := pcomp r2c r3c

@[expose] def trL (T0 : List ℕ) : List ℕ :=
  T0.flatMap fun t => [t, pcomp t r2c, pcomp t r3c, pcomp t r4c]

@[expose] def blk (k : ℕ) (L : List ℕ) : List ℕ := (L.drop (64 * k)).take 64

@[expose] def closedB (gs L : List ℕ) : Bool :=
  memB pid L && L.all fun a => gs.all fun g => memB (pcomp g a) L

@[expose] def inZB (T0 : List ℕ) (y : ℕ) : Bool := memB y T0 && t0g.all (commC y)

@[expose] def baseOK (T0 : List ℕ) : Bool :=
  Nat.beq T0.length 64 && nodupB T0 && nodupB (trL T0) && closedB t0g T0 &&
    T0.all (fun t => isId (psq (psq t))) &&
    isId (psq r2c) && isId (psq r3c) && isId (psq r4c) && !(memB r2c T0) && !(memB r3c T0) &&
    !(memB r4c T0) &&
    T0.all fun t => memB (pcomp (pcomp r2c t) r2c) T0 && memB (pcomp (pcomp r3c t) r3c) T0

@[expose] def centerOK (T0 Y : List ℕ) : Bool :=
  Y.all fun y => Nat.blt (T0.countP (commC y)) 32 || inZB T0 y

@[expose] def commOK (T0 : List ℕ) : Bool :=
  let Z := T0.filter (inZB T0)
  Nat.beq Z.length 4 && T0.all fun e => !(isId (psq e) && !(inZB T0 e)) ||
    Z.all fun z => T0.any fun t => Nat.beq (pcomp t e) (pcomp (pcomp e z) t)

@[expose] def rankOK (T0 TR : List ℕ) : Bool :=
  let I := TR.filter fun t => isId (psq t)
  Nat.blt (T0.countP fun t => isId (psq t)) 32 &&
    I.all fun e => memB e T0 || Nat.blt (I.countP (commC e)) 32

@[expose] def otherInv (y2 w : ℕ) : Bool := isId (psq w) && !(isId w) && !(Nat.beq w y2)

@[expose] def quatOK (T0 Y : List ℕ) : Bool :=
  Y.all fun y =>
    let y2 := psq y
    !(isId (psq y2) && !(isId y2)) ||
      (let cs := T0.map fun t => pcomp (pcomp t y) (pcube t)
       cs.any (fun c => otherInv y2 (pcomp y c)) ||
         cs.any fun c => let yc := pcomp y c; cs.any fun c' => otherInv y2 (pcomp yc c'))

@[expose] def unitOK (TR : List ℕ) : Bool :=
  let W := TR.filter fun t => commC t r4c
  Nat.beq W.length 32 && Nat.blt (W.countP fun t => isId (psq t)) 16 &&
    W.all fun y => isId (psq y) ||
      (let C := W.filter fun t => commC t y
       C.all fun a => C.all (commC a))

end CFSG.ComponentClassification.HSFLit.AutL34
