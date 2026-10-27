module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Sporadic.Th.Max3.DataBase

public section

namespace CFSG.KC.Th.Expr

inductive TE where
  | one
  | a
  | b
  | x
  | y
  | z
  | q (i : Fin 8)
  | nf (k : Fin 512)
  | nfE (s : Nat) (e : Fin 8 → Nat)
  | word (w : List CFSG.Sporadic.Th.Max3.Gen)
  | ab (w : List Nat)
  | prodFn (n : Nat) (f : Fin n → TE)
  | mul (e f : TE)
  | pow (e : TE) (n : Nat)

structure K where
  R : Nat → Nat
  c : Nat
  rm : Nat
  ONE : Nat
  SA : Nat
  SB : Nat

@[expose] noncomputable def K.mul (k : K) (P Q : Nat) : Nat := mulB k.c k.rm P Q

@[expose] noncomputable def K.pow (k : K) (P : Nat) : Nat → Nat
  | 0 => k.ONE
  | 1 => P
  | n + 2 => k.mul (k.pow P (n + 1)) P

@[expose] noncomputable def K.reg (k : K) (r : Nat) : Nat := k.mul k.ONE (k.R r)

@[expose] noncomputable def TE.pk (k : K) : TE → Nat
  | .one => k.ONE
  | .a => k.mul k.ONE k.SA
  | .b => k.mul k.ONE k.SB
  | .x => k.reg 13
  | .y => k.reg 14
  | .z => k.reg 16
  | .q i => k.reg (17 + i.val)
  | .nf j => k.reg (25 + j.val)
  | .nfE s e => k.mul (k.pow (k.reg 16) s)
      ((List.ofFn fun i : Fin 8 => k.pow (k.reg (17 + i.val)) (e i)).foldr k.mul k.ONE)
  | .word w => (w.map (CFSG.Sporadic.Th.Max3.Gen.eval (k.reg 13) (k.reg 14))).foldr k.mul k.ONE
  | .ab w => (w.map fun l => if l = 1 then k.mul k.ONE k.SA else k.mul k.ONE k.SB).foldr k.mul k.ONE
  | .prodFn _ f => (List.ofFn fun j => (f j).pk k).foldr k.mul k.ONE
  | .mul e f => k.mul (e.pk k) (f.pk k)
  | .pow e n => k.pow (e.pk k) n

@[expose] noncomputable def beqB (x b : Bool) : Bool := Bool.rec (BigS.notB x) x b

@[expose] noncomputable def pairsOK (k : K) : List (TE × TE × Bool) → Bool
  | [] => true
  | t :: l => andB (beqB (Nat.beq (t.1.pk k) (t.2.1.pk k)) t.2.2) (pairsOK k l)

end CFSG.KC.Th.Expr

end
