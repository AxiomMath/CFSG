module

public import CFSG.Certificates.Kernel.BabyMonster.F2

public section

namespace CFSG.KC.BM

@[expose] noncomputable def vm32 (k M v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih M v acc => forceB
      (Nat.xor acc (Nat.mul (Nat.land v (nat_lit 1)) (Nat.land M (nat_lit 4294967295))))
      (fun acc' => ih (Nat.shiftRight M (nat_lit 32)) (Nat.shiftRight v (nat_lit 1)) acc'))
    k M v (nat_lit 0)

@[expose] noncomputable def mm32 (k A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih A sh acc => forceB
      (Nat.lor acc (Nat.shiftLeft (vm32 k B (Nat.land A (nat_lit 4294967295))) sh))
      (fun acc' => ih (Nat.shiftRight A (nat_lit 32)) (Nat.add sh (nat_lit 32)) acc'))
    k A (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def id32 (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.shiftLeft (nat_lit 1) i) (Nat.mul (nat_lit 32) i))) k

@[expose] noncomputable def wf32 (k M : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight M (Nat.mul (nat_lit 32) k)) (nat_lit 0))
    (Nat.rec (motive := fun _ => Bool) true
      (fun i ih => andB ih (Nat.beq (Nat.shiftRight (Nat.land (Nat.shiftRight M (Nat.mul (nat_lit 32) i))
        (nat_lit 4294967295)) k) (nat_lit 0))) k)

@[expose] noncomputable def commBit (v0 vx : Nat) (Ws : List (List (List Nat))) : Nat :=
  forceB (vecW Ws v0) (fun w => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 18446744073709551616) (nat_lit 1) (Nat.beq w vx))
      (nat_lit 0) (Nat.beq w v0))

@[expose] noncomputable def app3 (A B : List (List (List Nat))) : List (List (List Nat)) :=
  List.rec (motive := fun _ => List (List (List Nat))) B (fun x _ ih => List.cons x ih) A

@[expose] noncomputable def pairBits (v0 vx : Nat) (A Es : List (List (List Nat))) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun E _ ih sh acc => forceB
      (Nat.add acc (Nat.shiftLeft (commBit v0 vx
        (app3 A (List.cons E (app3 A (List.cons E List.nil))))) sh))
      (fun acc' => ih (Nat.succ sh) acc'))
    Es (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def nthN (L : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) L i

@[expose] noncomputable def nthLL (L : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) L i

@[expose] noncomputable def nodeV (Vs : List (List Nat)) (k : Nat) : Nat :=
  nthN (nthLL Vs (Nat.shiftRight k (nat_lit 6))) (Nat.land k (nat_lit 63))

@[expose] noncomputable def fld4 (T k : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul (nat_lit 4) k)) (nat_lit 15)

@[expose] noncomputable def minN (a b : Nat) : Nat := Bool.rec (motive := fun _ => Nat) b a (Nat.ble a b)

@[expose] noncomputable def levOK (Vs : List (List Nat)) (LV GT : Nat) (Bs : List Nat) (k s : Nat) : Bool :=
  (fun lk g => Bool.rec (motive := fun _ => Bool)
      (andB (Nat.beq lk g) (andB (Nat.ble (Nat.sub g (nat_lit 1)) s)
        ((fun base => Nat.beq (vm32 (nat_lit 22) (nodeV Vs k) base) base) (nthN Bs (Nat.sub g (nat_lit 1))))))
      (Nat.ble lk s) (Nat.beq g (nat_lit 0)))
    (fld4 LV k) (fld4 GT k)

@[expose] noncomputable def nodeOK (Vs : List (List Nat)) (LV GT : Nat) (Bs : List Nat) (k e : Nat) : Bool :=
  (fun c b => andB (Nat.blt b k)
    (Bool.rec (motive := fun _ => Bool)
      (andB (andB (Nat.blt (Nat.sub c (nat_lit 1)) k)
          (Nat.beq (mm32 (nat_lit 22) (nodeV Vs (Nat.sub c (nat_lit 1))) (nodeV Vs b)) (nodeV Vs k)))
        (levOK Vs LV GT Bs k (minN (fld4 LV (Nat.sub c (nat_lit 1))) (fld4 LV b))))
      (andB (andB (wf32 (nat_lit 22) (nodeV Vs k))
          (Nat.beq (mm32 (nat_lit 22) (nodeV Vs k) (nodeV Vs b)) (id32 (nat_lit 22))))
        (levOK Vs LV GT Bs k (fld4 LV b)))
      (Nat.beq c (nat_lit 0))))
    (Nat.land e (nat_lit 8191)) (Nat.shiftRight e (nat_lit 13))

@[expose] noncomputable def nodesOK (Vs : List (List Nat)) (LV GT : Nat) (Bs : List Nat) (k0 : Nat)
    (es : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih k => andB (nodeOK Vs LV GT Bs k e) (ih (Nat.succ k))) es k0

@[expose] noncomputable def gensOK (GT g : Nat) (gs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (Nat.beq (fld4 GT x) g) ih) gs

@[expose] noncomputable def ptsOK (Vs : List (List Nat)) (LV : Nat) (L base prev : Nat) (es : List Nat) : Bool :=
  Nat.blt (nat_lit 0) (List.rec (motive := fun _ => Nat → Nat) (fun st => st)
    (fun e _ ih st =>
      (fun p w => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (ih (Nat.succ p))
          (andB (andB (Nat.blt (nat_lit 0) st) (Nat.ble st p))
            (andB (Nat.ble L (fld4 LV w)) (Nat.beq (vm32 (nat_lit 22) (nodeV Vs w) base) p))))
        (Nat.land e (nat_lit 4194303)) (Nat.shiftRight e (nat_lit 22)))
    es (Nat.succ prev))

end CFSG.KC.BM

end
