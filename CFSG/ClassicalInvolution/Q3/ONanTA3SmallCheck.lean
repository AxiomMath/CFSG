module

public import Mathlib.Algebra.Group.Defs
public import Aesop.BuiltinRules

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Check

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def memB (l : List M) (x : M) : Bool := l.any fun s => decide (s = x)

@[expose] def ordAux (o : M) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, k => if o ^ k = 1 then k else ordAux o fuel (k + 1)

@[expose] def ordB (B : ℕ) (o : M) : ℕ := ordAux o B 1

@[expose] def centB (L : List M) (t : M) : List M := L.filter fun c => decide (c * t = t * c)

@[expose] def noOddB (B : ℕ) (C : List M) : Bool :=
  C.all fun o => decide (ordB B o ≠ 0) &&
    (decide (o = 1) || decide (ordB B o % 2 = 0) ||
      C.any fun c => decide (ordB B (o * (c * o * c⁻¹)) ≠ 0) &&
        decide (ordB B (o * (c * o * c⁻¹)) % 2 = 0))

@[expose] def q8B (t a b : M) : List M := [1, a, t, t * a, b, b * a, b * t, b * (t * a)]

@[expose] def pairsB (t : M) (C : List M) : Bool :=
  (C.filter fun a => decide (a * a = t)).all fun a =>
    (C.filter fun b => decide (b * b = t)).all fun b =>
      !decide (b * a = t * a * b) ||
      !(C.all fun c => memB (q8B t a b) (c * a * c⁻¹) && memB (q8B t a b) (c * b * c⁻¹)) ||
      C.any fun x => decide (x ^ 3 = 1) && !decide (x * a = a * x ∧ x * b = b * x) &&
        C.all fun y => !decide (y * a = a * y ∧ y * b = b * y) || decide (x * y = y * x)

@[expose] def goodCheck (B : ℕ) (L : List M) : Bool :=
  L.all fun t => !decide (t * t = 1 ∧ t ≠ 1) ||
    (let C := centB L t; noOddB B C && pairsB t C)

end CFSG.ClassicalInvolution.Q3.TA3.Check
