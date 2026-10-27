module

public import CFSG.Certificates.Kernel.BabyMonster.B64
public import Certificates.Data.Kernel.YModel.Text

public section

namespace CFSG.KC.BM.Lat

open CFSG.KC.BM CFSG.KC.BM.B64 CFSG.KC.YModel

@[expose] noncomputable def ones (k : Nat) : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) k) (nat_lit 1)

@[expose] noncomputable def spread (d : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun x n => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k ih => Nat.lor ih (Nat.shiftLeft (Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 7) k))
        (nat_lit 127)) (Nat.mul (nat_lit 16) k))) n)
    (fun _ ih x n => (fun m => Nat.lor (ih (Nat.land x (ones (Nat.mul (nat_lit 7) m))) m)
        (Nat.shiftLeft (ih (Nat.shiftRight x (Nat.mul (nat_lit 7) m)) (Nat.sub n m))
          (Nat.mul (nat_lit 16) m)))
      (Nat.div n (nat_lit 2))) d

@[expose] noncomputable def entBefore (i : Nat) : Nat :=
  Nat.sub (Nat.mul (nat_lit 4370) i) (Nat.div (Nat.mul i (Nat.sub i (nat_lit 1))) (nat_lit 2))

@[expose] noncomputable def recOf (Bs : List (List Nat)) (i : Nat) : Nat :=
  lget (lgetL Bs (Nat.div i (nat_lit 64))) (Nat.mod i (nat_lit 64))

@[expose] noncomputable def isB64 (c : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) (Nat.beq c (nat_lit 61)) true (Nat.beq c (nat_lit 47)))
          true (Nat.beq c (nat_lit 43)))
        true (inR (nat_lit 48) (nat_lit 57) c))
      true (inR (nat_lit 97) (nat_lit 122) c))
    true (inR (nat_lit 65) (nat_lit 90) c)

@[expose] noncomputable def isNilP (L : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L

@[expose] noncomputable def pieceOK (last : Bool) (p : Nat × Nat) : Bool :=
  andB (Bool.rec (motive := fun _ => Bool) (Nat.beq p.2 (nat_lit 256)) (Nat.ble p.2 (nat_lit 256))
      last)
    (Nat.rec (motive := fun _ => Bool) true
      (fun k ih => andB ih (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (chAt p.1 k) (nat_lit 10)) (andB (Nat.beq (Nat.succ k) p.2) last))
        true (isB64 (chAt p.1 k)))) p.2)

@[expose] noncomputable def winOf (L : List (Nat × Nat)) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun p t ih c m acc => Bool.rec (motive := fun _ => Nat) acc
      (Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) (nat_lit 1073741824))
        (forceB (Nat.lor acc (Nat.shiftLeft (segDec p.1 (nat_lit 64)) (Nat.mul (nat_lit 1536) m)))
          (fun a => ih (Nat.sub c (nat_lit 1)) (Nat.succ m) a))
        (pieceOK (isNilP t) p))
      (Nat.blt (nat_lit 0) c))
    L c (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def rowOK (Bs : List (List Nat)) (W b0 i : Nat) : Bool :=
  (fun n => Nat.beq
      (spread (nat_lit 13)
        (Nat.land (Nat.shiftRight W (Nat.sub (Nat.mul (nat_lit 7) (entBefore i)) b0))
          (ones (Nat.mul (nat_lit 7) n))) n)
      (Nat.shiftRight (recOf Bs i) (nat_lit 16)))
    (Nat.sub (nat_lit 4370) i)

@[expose] noncomputable def rowsOK (L : List (Nat × Nat)) (Bs : List (List Nat)) (i c : Nat) :
    Bool :=
  (fun p0 pe => (fun W => Nat.rec (motive := fun _ => Bool) true
      (fun k ih => andB ih (rowOK Bs W (Nat.mul (nat_lit 1536) p0) (Nat.add i k))) c)
    (winOf (dropP L (Nat.succ p0)) (Nat.sub pe p0)))
    (Nat.div (Nat.mul (nat_lit 7) (entBefore i)) (nat_lit 1536))
    (Nat.div (Nat.add (Nat.mul (nat_lit 7) (entBefore (Nat.add i c))) (nat_lit 1535)) (nat_lit 1536))

@[expose] noncomputable def diagOK (p : Nat × Nat) (Bs : List (List Nat)) : Bool :=
  andB (Nat.beq p.2 (nat_lit 4372)) (andB (Nat.beq (chAt p.1 (nat_lit 4371)) (nat_lit 10))
    (Nat.rec (motive := fun _ => Bool) true
      (fun i ih => andB ih (andB (inR (nat_lit 48) (nat_lit 55) (chAt p.1 i))
        (Nat.beq (Nat.land (recOf Bs i) (nat_lit 65535))
          (Nat.shiftLeft (nat_lit 1) (Nat.sub (chAt p.1 i) (nat_lit 48))))))
      (nat_lit 4371)))

end CFSG.KC.BM.Lat

end
