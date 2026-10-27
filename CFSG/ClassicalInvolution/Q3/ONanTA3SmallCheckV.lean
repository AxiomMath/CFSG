module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheck

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Check

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def noOddB3 (B : ℕ) (C : List M) : Bool :=
  C.all fun o => decide (ordB B o ≠ 0) &&
    (decide (o = 1) || decide (ordB B o % 2 = 0) ||
      (C.any fun c => decide (ordB B (o * (c * o * c⁻¹)) ≠ 0) &&
        decide (ordB B (o * (c * o * c⁻¹)) % 2 = 0)) ||
      (C.any fun c => C.any fun d =>
        decide (ordB B (o * (c * o * c⁻¹) * (d * o * d⁻¹)) ≠ 0) &&
          decide (ordB B (o * (c * o * c⁻¹) * (d * o * d⁻¹)) % 2 = 0)))

@[expose] def edgelessB (L : List M) (t a b : M) : Bool :=
  L.all fun g => !((q8B t a b).all fun r => decide (g * r * g⁻¹ * t = t * (g * r * g⁻¹))) ||
    (q8B t a b).any fun r => decide (g * r * g⁻¹ = t)

@[expose] def noActs3B (B : ℕ) (C : List M) (a b : M) : Bool :=
  C.all fun x => decide (ordB B x ≠ 0) &&
    !(decide (ordB B x = 9) || decide (ordB B x = 27) || decide (ordB B x = 81)) &&
    (!decide (ordB B x = 1 ∨ ordB B x = 3) || decide (x * a = a * x ∧ x * b = b * x))

@[expose] def pairsV (B : ℕ) (LN L : List M) (e3b : Bool) (t : M) (C : List M) : Bool :=
  (C.filter fun a => decide (a * a = t)).all fun a =>
    (C.filter fun b => decide (b * b = t)).all fun b =>
      !decide (b * a = t * a * b) ||
      !(C.all fun c => memB (q8B t a b) (c * a * c⁻¹) && memB (q8B t a b) (c * b * c⁻¹)) ||
      (memB LN a && memB LN b) ||
      (C.any fun x => decide (x ^ 3 = 1) && !decide (x * a = a * x ∧ x * b = b * x) &&
        C.all fun y => !decide (y * a = a * y ∧ y * b = b * y) || decide (x * y = y * x)) ||
      (edgelessB L t a b && (e3b || noActs3B B C a b))

@[expose] def isCovered (L reps : List M) (t : M) : Bool :=
  L.any fun g => reps.any fun r => decide (g * t * g⁻¹ = r)

@[expose] def coverB (reps L : List M) : Bool :=
  L.all fun t => !decide (t * t = 1 ∧ t ≠ 1) || isCovered L reps t

@[expose] def pickReps (L : List M) : List M :=
  L.foldl (fun reps t => if decide (t * t = 1 ∧ t ≠ 1) && !isCovered L reps t then reps ++ [t]
    else reps) []

@[expose] def verdictCheck (B : ℕ) (LN L : List M) (e3b : Bool) (reps : List M) : Bool :=
  coverB reps L && reps.all fun t => (let C := centB L t; noOddB3 B C && pairsV B LN L e3b t C)

end CFSG.ClassicalInvolution.Q3.TA3.Check
