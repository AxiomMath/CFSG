module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSurvData

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def pcBits : Array ℕ :=
  #[1, 512, 2050, 3076, 8200, 12304, 2054, 1028, 32, 16384, 131200, 196864, 8216, 4112, 131456,
    65792, 64, 32768]

@[expose] def pciBits : Array ℕ :=
  #[1, 140, 68, 8240, 4112, 256, 65536, 35840, 17408, 2, 196, 136, 12304, 8224, 512, 131072,
    50176, 34816]

@[expose] def mulN (a b : ℕ) : ℕ :=
  (a % 2 * (b % 2) + a / 2 % 2 * (b / 2 % 2)) % 2 +
    2 * ((a % 2 * (b / 2 % 2) + a / 2 % 2 * (b % 2) + a / 2 % 2 * (b / 2 % 2)) % 2)

@[expose] def krCode (A B : Fin 3 → Fin 3 → ℕ) (r s : Fin 9) : ℕ :=
  mulN (A ⟨(r : ℕ) / 3, by omega⟩ ⟨(s : ℕ) / 3, by omega⟩)
    (B ⟨(r : ℕ) % 3, by omega⟩ ⟨(s : ℕ) % 3, by omega⟩)

@[expose] def reBits9 (M : Fin 9 → Fin 9 → ℕ) : Array ℕ :=
  Array.ofFn (n := 18) fun r => bitsOf 18 fun col =>
    reBit (M ⟨(r : ℕ) / 2, by omega⟩ (Fin.ofNat 9 (col / 2))) ((r : ℕ) % 2) (col % 2)

@[expose] def trCode3 (a b : Fin 3) (k : ℕ) (i j : Fin 3) : ℕ :=
  if i = j then 1 else if i = a ∧ j = b then k else 0

@[expose] def kactBits (A : Fin 3 → Fin 3 → ℕ) : Array ℕ :=
  bmul 18 18 (bmul 18 18 pciBits (reBits9 (krCode A fun i j => frobCode (A i j)))) pcBits

@[expose] def bd9Bits (A B : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 18) fun r =>
    if (r : ℕ) < 9 then A.getD r 0 % 512 else (B.getD (r - 9) 0 % 512) <<< 9

@[expose] def pairOf (s : Fin 12) : Fin 3 × Fin 3 :=
  match (s : ℕ) / 2 with
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (1, 0)
  | 3 => (1, 2)
  | 4 => (2, 0)
  | _ => (2, 1)

@[expose] def coefCode (s : Fin 12) : ℕ := if (s : ℕ) % 2 = 0 then 1 else 2

@[expose] def genABits : Fin 12 → Array ℕ
  | 0 => #[37, 34, 4, 136, 272, 32, 64, 128, 256]
  | 1 => #[35, 2, 36, 264, 400, 32, 64, 128, 256]
  | 2 => #[81, 386, 260, 72, 16, 32, 64, 128, 256]
  | 3 => #[73, 258, 132, 8, 80, 32, 64, 128, 256]
  | 4 => #[1, 3, 4, 8, 16, 37, 64, 136, 272]
  | 5 => #[1, 3, 5, 8, 16, 39, 64, 144, 280]
  | 6 => #[1, 10, 20, 8, 16, 352, 64, 192, 256]
  | 7 => #[1, 26, 12, 8, 16, 224, 64, 128, 320]
  | 8 => #[1, 2, 4, 9, 16, 32, 81, 134, 260]
  | 9 => #[1, 2, 4, 9, 17, 32, 89, 130, 262]
  | 10 => #[1, 2, 4, 10, 20, 32, 352, 160, 256]
  | 11 => #[1, 2, 4, 14, 18, 32, 480, 160, 288]

@[expose] def kGenCheck : Bool :=
  (List.finRange 12).all fun s =>
    kactBits (trCode3 (pairOf s).1 (pairOf s).2 (coefCode s)) == bd9Bits (genABits s) (genABits s)

@[expose] def genIdx (a b : Fin 3) (β : ℕ) : Fin 12 :=
  Fin.ofNat 12 (2 * (if a = 0 then (if b = 1 then 0 else 1) else if a = 1 then
    (if b = 0 then 2 else 3) else (if b = 0 then 4 else 5)) + β)

@[expose] def wordX (a b : Fin 3) (k : ℕ) : List (Fin 12) :=
  if k % 4 = 0 then [] else if k % 4 = 1 then [genIdx a b 0] else if k % 4 = 2 then [genIdx a b 1]
  else [genIdx a b 0, genIdx a b 1]

@[expose] def relWord (a b : Fin 3) (c : ℕ) (d e : Fin 3) (f : ℕ) : List (Fin 12) :=
  wordX a b c ++ wordX d e f ++ (wordX a b c).reverse ++ (wordX d e f).reverse ++
    (if b = d then wordX a e (mulN c f) else if a = e then wordX d b (mulN c f) else []).reverse

@[expose] def commRels : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(0, 1, 1, 0, 1, 2), (0, 1, 1, 0, 2, 1), (0, 1, 1, 0, 2, 2), (0, 1, 2, 0, 2, 1),
    (0, 1, 2, 0, 2, 2), (0, 1, 1, 1, 2, 1), (0, 1, 1, 1, 2, 2), (0, 1, 1, 1, 2, 3),
    (0, 1, 2, 1, 2, 1), (0, 1, 2, 1, 2, 2), (0, 1, 1, 2, 0, 1), (0, 1, 1, 2, 0, 2),
    (0, 1, 1, 2, 0, 3), (0, 1, 2, 2, 0, 1), (0, 1, 2, 2, 0, 2), (0, 2, 1, 1, 0, 1),
    (0, 2, 1, 1, 0, 2), (0, 2, 1, 1, 0, 3), (0, 2, 2, 1, 0, 1), (0, 2, 2, 1, 0, 2),
    (0, 2, 1, 2, 1, 1), (0, 2, 1, 2, 1, 2), (0, 2, 2, 2, 1, 1), (0, 2, 2, 2, 1, 2),
    (1, 0, 1, 1, 0, 2), (1, 0, 1, 2, 0, 1), (1, 0, 1, 2, 0, 2), (1, 0, 2, 2, 0, 1),
    (1, 0, 1, 2, 1, 1), (1, 0, 1, 2, 1, 2), (1, 2, 1, 2, 0, 1), (1, 2, 1, 2, 0, 2)]

@[expose] def commWord (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : List (Fin 12) :=
  relWord (Fin.ofNat 3 t.1) (Fin.ofNat 3 t.2.1) t.2.2.1 (Fin.ofNat 3 t.2.2.2.1)
    (Fin.ofNat 3 t.2.2.2.2.1) t.2.2.2.2.2

@[expose] def h1Rels3 : List (List (Fin 12)) :=
  (List.finRange 12).map (fun s => [s, s]) ++ commRels.map commWord

@[expose] def commValid : Bool :=
  commRels.all fun t => t.1 < 3 && t.2.1 < 3 && t.2.2.2.1 < 3 && t.2.2.2.2.1 < 3 &&
    t.1 != t.2.1 && t.2.2.2.1 != t.2.2.2.2.1 &&
    !(t.2.2.2.1 == t.2.1 && t.2.2.2.2.1 == t.1) && t.2.2.1 < 4 && t.2.2.2.2.2 < 4

@[expose] def id9 : Array ℕ := #[1, 2, 4, 8, 16, 32, 64, 128, 256]

@[expose] def zero9 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def urPair9 (C : Fin 12 → Array ℕ) : List (Fin 12) → Array ℕ × Array ℕ
  | [] => (id9, zero9)
  | s :: w =>
    let p := urPair9 C w
    (bmul 9 9 (genABits s) p.1, bxor 9 (bmul 9 9 (genABits s) p.2) (bmul 9 9 (C s) p.1))

@[expose] def h1Fb9 (v : ℕ) : ℕ :=
  packN 9 44 fun k => (urPair9 (fun s => unpackN 9 v s) (h1Rels3.getD k [])).2

@[expose] def cobFb9 (v : ℕ) : ℕ :=
  packN 9 12 fun s =>
    bxor 9 (bmul 9 9 (genABits (Fin.ofNat 12 s)) (unpackN 9 v 0))
      (bmul 9 9 (unpackN 9 v 0) (genABits (Fin.ofNat 12 s)))

@[expose] def h1Check9 : Bool :=
  certCheck (12 * (9 * 9)) 81 (44 * (9 * 9)) (linBits (12 * (9 * 9)) (44 * (9 * 9)) h1Fb9)
    (Array.ofFn (n := 81) fun j => cobFb9 (2 ^ (j : ℕ)))

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
