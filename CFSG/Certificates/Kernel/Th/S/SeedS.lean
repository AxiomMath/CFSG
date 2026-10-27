module

public import Certificates.Data.CFSGNative.Th.Data
public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Th.Words

public section

namespace CFSG.KC.Th.SeedS

open CFSG.KC.Th CFSG.KC.Loop CFSG.Sporadic.Th.Native

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def isWs (n : Nat) : Bool :=
  orB (Nat.beq n (nat_lit 32)) (orB (Nat.beq n (nat_lit 9)) (orB (Nat.beq n (nat_lit 10))
    (orB (Nat.beq n (nat_lit 13)) (orB (Nat.beq n (nat_lit 11)) (Nat.beq n (nat_lit 12))))))

@[expose] noncomputable def ent2 (n : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.land (Nat.sub n (nat_lit 48)) (nat_lit 1))
    (andB (Nat.ble (nat_lit 48) n) (Nat.ble n (nat_lit 57)))

@[expose] noncomputable def row256 (M i : Nat) : Nat :=
  Nat.land (Nat.shiftRight M (Nat.mul (nat_lit 256) i))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) (nat_lit 1))

@[expose] noncomputable def decRun (M : Nat) (l : List Char) : Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun _ i _ acc => Nat.beq (Nat.shiftRight M (Nat.mul (nat_lit 256) i)) acc)
    (fun ch _ ih ph i j acc => strictB (Char.toNat ch) fun n =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (ih (nat_lit 0) i j acc) (ih (nat_lit 1) i j acc)
          (Nat.beq n (nat_lit 10)))
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (strictB (Nat.add acc (Nat.shiftLeft (ent2 n) j)) fun a => strictB (Nat.succ j) fun j1 =>
              Bool.rec (motive := fun _ => Bool) (ih (nat_lit 1) i j1 a)
                (andB (Nat.beq (row256 M i) a)
                  (strictB (Nat.succ i) fun i1 => ih (nat_lit 1) i1 (nat_lit 0) (nat_lit 0)))
                (Nat.beq j1 (nat_lit 248)))
            (ih (nat_lit 1) i j acc) (Nat.ble (nat_lit 248) i))
          (ih (nat_lit 1) i j acc) (isWs n))
        (Nat.beq ph (nat_lit 1)))
    l

@[expose] noncomputable def decOK (M : Nat) (l : List Char) : Bool :=
  decRun M l (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def v4Nat (v : V4) : Nat :=
  Nat.lor (UInt64.toNat v.w0) (Nat.lor (Nat.shiftLeft (UInt64.toNat v.w1) (nat_lit 64))
    (Nat.lor (Nat.shiftLeft (UInt64.toNat v.w2) (nat_lit 128))
      (Nat.shiftLeft (UInt64.toNat v.w3) (nat_lit 192))))

@[expose] noncomputable def packFrom (l : List V4) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun r => Nat.shiftLeft r (nat_lit 65536))
    (fun v _ ih r => Nat.lor (Nat.shiftLeft (v4Nat v) (Nat.mul (nat_lit 256) r)) (ih (Nat.succ r))) l

@[expose] noncomputable def packOK (M : Nat) (l : List V4) : Bool :=
  Nat.beq (packFrom l (nat_lit 0)) (Nat.lor M (Nat.shiftLeft (nat_lit 248) (nat_lit 65536)))

@[expose] noncomputable def fcRowsList : List V4 := fcRows.toList

end CFSG.KC.Th.SeedS
