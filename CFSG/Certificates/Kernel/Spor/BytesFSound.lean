module

public import Certificates.Data.Kernel.Spor.BytesF

public section

namespace CFSG.KS.Bytes

theorem strictB_eq (y : Nat) (k : Nat → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

theorem run_eq_runF (F : Nat → Nat) (lb len : Nat) :
    ∀ (cs : List Char) (i : Nat), run F lb len cs i = runF F lb len cs i := by
  intro cs
  induction cs with
  | nil => intro i; rfl
  | cons ch cs ih =>
    intro i
    show (fun b => bAnd(Nat.blt (Char.toNat ch) (nat_lit 128), bAnd(Nat.blt i len,
        bAnd(Nat.beq (Char.toNat ch) (fld(F (Nat.div i lb), Nat.mul (nat_lit 8) (Nat.mod i lb),
          nat_lit 255)), b)))) (run F lb len cs (Nat.succ i)) =
      (fun b => bAnd(Nat.blt (Char.toNat ch) (nat_lit 128), bAnd(Nat.blt i len,
        bAnd(Nat.beq (Char.toNat ch) (fld(F (Nat.div i lb), Nat.mul (nat_lit 8) (Nat.mod i lb),
          nat_lit 255)), b)))) (CFSG.KC.M1F2.strictB (Nat.succ i) (runF F lb len cs))
    rw [strictB_eq, ih]

theorem bytesEqK_of_runF {cs : List Char} {F : Nat → Nat} {lb len : Nat} (hlb : 0 < lb)
    (h : runF F lb len cs 0 = true) : bytesEqK cs F lb len = true := by
  have e : bytesEqK cs F lb len = bAnd(Nat.blt (nat_lit 0) lb, run F lb len cs (nat_lit 0)) := rfl
  rw [e, run_eq_runF]
  change bAnd(Nat.blt 0 lb, runF F lb len cs 0) = true
  rw [h, Nat.blt_eq.mpr hlb]

end CFSG.KS.Bytes

end
