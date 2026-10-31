
module

public import Certificates.Data.Kernel.ThCent.Pin
public import CFSG.Certificates.Kernel.Th.Spec.FwdRelBase

@[expose] public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel CFSG.SectionRank.Native
  CFSG.Sporadic.Th

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem strictF_eq {α : Sort*} (y : ℕ) (k : ℕ → α) : strictF y k = k y := by
  cases y <;> rfl

theorem beq_false' {m n : ℕ} (h : m ≠ n) : Nat.beq m n = false :=
  Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

def opG {G : Type*} [Group G] (R : ℕ → G) : Op → ℕ → G
  | .mul i j k => Function.update R k (R i * R j)
  | .pow e i k => Function.update R k (R i ^ e)

def initG {G : Type*} [Group G] (g h : G) : ℕ → G := fun r =>
  if r = 0 then g else if r = 1 then h else 1

def slpG {G : Type*} [Group G] (g h : G) (prog : List Op) : ℕ → G :=
  prog.foldl opG (initG g h)

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  {J : Subgroup (GL (Fin 248) (ZMod 2))}
  (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
include hk

end CFSG.KC.ThCent

end
