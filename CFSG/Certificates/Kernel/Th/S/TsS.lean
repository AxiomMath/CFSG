module

public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Certificates.Kernel.Th.Big

public section

namespace CFSG.KC.Th.TsS

open CFSG.KC.Th CFSG.KC.Loop CFSG.KC.Th.SeedS

@[expose] noncomputable def decV (n : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 10) (Nat.sub n (nat_lit 48))
    (andB (Nat.ble (nat_lit 48) n) (Nat.ble n (nat_lit 57)))

@[expose] noncomputable def hexV (n : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 16) (Nat.sub n (nat_lit 55))
        (andB (Nat.ble (nat_lit 65) n) (Nat.ble n (nat_lit 70))))
      (Nat.sub n (nat_lit 87)) (andB (Nat.ble (nat_lit 97) n) (Nat.ble n (nat_lit 102))))
    (Nat.sub n (nat_lit 48)) (andB (Nat.ble (nat_lit 48) n) (Nat.ble n (nat_lit 57)))

@[expose] noncomputable def isSep (n : Nat) : Bool := orB (Nat.beq n (nat_lit 32)) (Nat.beq n (nat_lit 10))

@[expose] noncomputable def natsGo (T : Nat → Nat) (n : Nat) (hex : Bool) (l : List Char) :
    Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun ph i acc => Bool.rec (motive := fun _ => Bool)
      (andB (Nat.beq ph (nat_lit 1)) (andB (Nat.beq (T i) acc) (Nat.beq (Nat.succ i) n)))
      (Nat.beq i n) (Nat.beq ph (nat_lit 0)))
    (fun ch _ ih ph i acc => strictB (Char.toNat ch) fun c =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (strictB (decV c) fun d => Bool.rec (motive := fun _ => Bool)
            (strictB (Nat.add (Nat.mul (nat_lit 10) acc) d) fun a => ih (nat_lit 1) i a)
            false (Nat.beq d (nat_lit 10)))
          (Bool.rec (motive := fun _ => Bool)
            (Bool.rec (motive := fun _ => Bool)
              (strictB (hexV c) fun d => Bool.rec (motive := fun _ => Bool)
                (strictB (Nat.add (Nat.mul (nat_lit 16) acc) d) fun a => ih (nat_lit 1) i a)
                false (Nat.beq d (nat_lit 16)))
              (Bool.rec (motive := fun _ => Bool) false (ih (nat_lit 3) i (nat_lit 0))
                (Nat.beq c (nat_lit 120)))
              (Nat.beq ph (nat_lit 2)))
            (Bool.rec (motive := fun _ => Bool) false (ih (nat_lit 2) i (nat_lit 0))
              (Nat.beq c (nat_lit 48)))
            (Nat.beq ph (nat_lit 0)))
          hex)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) false
            (andB (Nat.beq (T i) acc) (strictB (Nat.succ i) fun i1 => ih (nat_lit 0) i1 (nat_lit 0)))
            (Nat.beq ph (nat_lit 1)))
          (ih (nat_lit 0) i acc) (Nat.beq ph (nat_lit 0)))
        (isSep c))
    l

@[expose] noncomputable def natsRun (T : Nat → Nat) (n : Nat) (hex : Bool) (l : List Char) : Bool :=
  natsGo T n hex l (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def items (f : Nat → Bool) (C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun _ ih S => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (strictN (Nat.succ S) ih) (andB (Nat.blt (nat_lit 0) S) (f (Nat.sub S (nat_lit 1))))) C S

@[expose] noncomputable def runItems (f : Nat → Bool) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun C _ ih S => strictN (items f C S) ih) Cs

@[expose] noncomputable def permOK (ROWS PX PY : Nat → Nat) (rm LX LY2 n i : Nat) : Bool :=
  andB (Nat.blt (PX i) n) (andB (Nat.blt (PY i) n)
    (andB (Nat.beq (vecB rm (ROWS i) LX) (ROWS (PX i))) (Nat.beq (vecB rm (ROWS i) LY2) (ROWS (PY i)))))

@[expose] noncomputable def invOK (TP INV : Nat → Nat) (n i : Nat) : Bool :=
  andB (Nat.blt (INV i) n) (Nat.beq (TP (INV i)) i)

@[expose] noncomputable def treeOK (TP TPar TLab PX PY : Nat → Nat) (n k : Nat) : Bool :=
  andB (Nat.blt (TP k) n)
    (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (TPar k) k)
        (orB (andB (Nat.beq (TLab k) (nat_lit 1)) (Nat.beq (PX (TP (TPar k))) (TP k)))
          (andB (Nat.beq (TLab k) (nat_lit 2)) (Nat.beq (PY (TP (TPar k))) (TP k)))))
      true (Nat.beq k (nat_lit 0)))

end CFSG.KC.Th.TsS
