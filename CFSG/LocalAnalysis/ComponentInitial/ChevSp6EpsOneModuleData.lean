module

public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne.ExtOne

@[expose] def nb (n k : ℕ) : ℕ := n / 2 ^ k % 2

@[expose] def dot3 (a b c d e f : ℕ) : ℕ := (a * d + b * e + c * f) % 2

@[expose] def mul9 (x y : ℕ) : ℕ :=
  dot3 (nb x 0) (nb x 1) (nb x 2) (nb y 0) (nb y 3) (nb y 6) +
  2 * dot3 (nb x 0) (nb x 1) (nb x 2) (nb y 1) (nb y 4) (nb y 7) +
  4 * dot3 (nb x 0) (nb x 1) (nb x 2) (nb y 2) (nb y 5) (nb y 8) +
  8 * dot3 (nb x 3) (nb x 4) (nb x 5) (nb y 0) (nb y 3) (nb y 6) +
  16 * dot3 (nb x 3) (nb x 4) (nb x 5) (nb y 1) (nb y 4) (nb y 7) +
  32 * dot3 (nb x 3) (nb x 4) (nb x 5) (nb y 2) (nb y 5) (nb y 8) +
  64 * dot3 (nb x 6) (nb x 7) (nb x 8) (nb y 0) (nb y 3) (nb y 6) +
  128 * dot3 (nb x 6) (nb x 7) (nb x 8) (nb y 1) (nb y 4) (nb y 7) +
  256 * dot3 (nb x 6) (nb x 7) (nb x 8) (nb y 2) (nb y 5) (nb y 8)

@[expose] def add9 (x y : ℕ) : ℕ :=
  (nb x 0 + nb y 0) % 2 + 2 * ((nb x 1 + nb y 1) % 2) + 4 * ((nb x 2 + nb y 2) % 2) +
  8 * ((nb x 3 + nb y 3) % 2) + 16 * ((nb x 4 + nb y 4) % 2) + 32 * ((nb x 5 + nb y 5) % 2) +
  64 * ((nb x 6 + nb y 6) % 2) + 128 * ((nb x 7 + nb y 7) % 2) + 256 * ((nb x 8 + nb y 8) % 2)

@[expose] def oneN : ℕ := 273

@[expose] def pmulN (p q : ℕ × ℕ) : ℕ × ℕ :=
  (mul9 p.1 q.1, add9 (mul9 p.1 q.2) (mul9 p.2 q.1))

@[expose] def ppowN (p : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => (oneN, 0)
  | n + 1 => pmulN (ppowN p n) p

@[expose] def aN : ℕ := 275

@[expose] def bN : ℕ := 140

@[expose] def extRelA (x : ℕ) : Bool := pmulN (aN, x) (aN, x) == (oneN, 0)

@[expose] def extRelB (y : ℕ) : Bool := ppowN (bN, y) 3 == (oneN, 0)

@[expose] def extRelAB (x y : ℕ) : Bool := ppowN (pmulN (aN, x) (bN, y)) 7 == (oneN, 0)

@[expose] def extCob (x y m : ℕ) : Bool :=
  x == add9 (mul9 aN m) (mul9 m aN) && y == add9 (mul9 bN m) (mul9 m bN)

@[expose] def extCheck : Bool :=
  (List.range 512).all fun x => !extRelA x || (List.range 512).all fun y => !extRelB y ||
    !extRelAB x y || (List.range 512).any fun m => extCob x y m

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne.ExtOne
