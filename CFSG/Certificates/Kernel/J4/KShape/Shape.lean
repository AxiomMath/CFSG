module

public import CFSG.Certificates.Kernel.J4.KRSData

public section

namespace CFSG.KJ4.KShape

open CFSG.KJ4 CFSG.KJ4.S

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def rcat (A B : Nat) : Nat :=
  Nat.lor (Nat.add (wN A) (wN B)) (Nat.shiftLeft (wCat (wW A) (wN A) (wW B)) (nat_lit 32))

@[expose] noncomputable def rinv (INV A : Nat) : Nat :=
  Nat.lor (wN A) (Nat.shiftLeft (wInv INV (wW A) (wN A)) (nat_lit 32))

@[expose] noncomputable def lit (c : Nat) : Nat := Nat.lor (nat_lit 1) (Nat.shiftLeft c (nat_lit 32))

@[expose] def WREC : Nat :=
  nat_lit 0x20002020002000000000700000000000000020200020000000006000000000000000202000200000000050000000000000000020002000000000500000000000000000002020000000004000000000000000002000200000000040000000000000000000202000000000300000000000000000000020000000003000000000000000000000200000000020000000000000000000000000000000100000000000000000000000000000000

@[expose] def CM : Nat :=
  nat_lit 0x75404a0040001000008020000940020014e0010010000800002004000200004001000080004000100010002

@[expose] noncomputable def wrec (WT i : Nat) : Nat :=
  Nat.land (Nat.shiftRight WT (Nat.mul (nat_lit 128) i))
    (nat_lit 340282366920938463463374607431768211455)

@[expose] noncomputable def zr (INV WT i e : Nat) : Nat :=
  rcat (rcat (rinv INV (wrec WT i)) (lit e)) (wrec WT i)

@[expose] noncomputable def prodW (INV WT c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun k ih acc => ih (Bool.rec (motive := fun _ => Nat) acc
      (rcat acc (zr INV WT (Nat.sub (nat_lit 10) k) (nat_lit 5)))
      (Nat.blt (nat_lit 0) (Nat.land c (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 10) k))))))
    (nat_lit 11) (nat_lit 0)

@[expose] noncomputable def same (INV R E : Nat) : Bool :=
  andB (wFits (wW R) (wN R)) (Nat.beq (freeRed INV (wW E) (wN E)) (freeRed INV (wW R) (wN R)))

@[expose] noncomputable def pairIdx (i j : Nat) : Nat :=
  Nat.add (nat_lit 10) (Nat.sub (Nat.add (Nat.div (Nat.mul i (Nat.sub (nat_lit 21) i)) (nat_lit 2)) j) i)

@[expose] noncomputable def wordsOK (WT : Nat) : Bool :=
  andB (Nat.beq (wrec WT (nat_lit 0)) (nat_lit 0))
    (rngAll (nat_lit 0) (nat_lit 11) (nat_lit 1) (fun i =>
      andB (wFits (wW (wrec WT i)) (wN (wrec WT i))) (letsBelow (wW (wrec WT i)) (wN (wrec WT i)) (nat_lit 4))))

@[expose] noncomputable def sqOK (RZT : Nat → Nat) (INV WT : Nat) : Bool :=
  rngAll (nat_lit 0) (nat_lit 11) (nat_lit 1) (fun i =>
    same INV (RZT i) (rcat (zr INV WT i (nat_lit 5)) (zr INV WT i (nat_lit 5))))

@[expose] noncomputable def commOK (RZT : Nat → Nat) (INV WT lo hi : Nat) : Bool :=
  rngAll lo hi (nat_lit 1) (fun i => rngAll (Nat.succ i) (nat_lit 11) (nat_lit 1) (fun j =>
    same INV (RZT (pairIdx i j))
      (rcat (rcat (zr INV WT i (nat_lit 6)) (zr INV WT j (nat_lit 6))) (rcat (zr INV WT i (nat_lit 5)) (zr INV WT j (nat_lit 5))))))

@[expose] noncomputable def conjOK (RZT : Nat → Nat) (INV WT C : Nat) : Bool :=
  rngAll (nat_lit 0) (nat_lit 22) (nat_lit 1) (fun q =>
    (fun i g => same INV (RZT (Nat.add (nat_lit 66) q))
      (rcat (rcat (rcat (lit (Nat.succ g)) (zr INV WT i (nat_lit 5))) (lit g))
        (rinv INV (prodW INV WT (Nat.land (Nat.shiftRight C (Nat.mul (nat_lit 16) q)) (nat_lit 65535))))))
    (Nat.div q (nat_lit 2)) (Nat.mul (nat_lit 2) (Nat.mod q (nat_lit 2))))

theorem inv_ok : Nat.beq CFSG.KJ4.KRS.INV (nat_lit 0x5060402030001) = true := by quickRfl

theorem words_ok : wordsOK WREC = true := by quickRfl

theorem sq_ok : sqOK CFSG.KJ4.KRS.RZT CFSG.KJ4.KRS.INV WREC = true := by quickRfl

theorem comm_ok0 : commOK CFSG.KJ4.KRS.RZT CFSG.KJ4.KRS.INV WREC (nat_lit 0) (nat_lit 3) = true := by quickRfl

theorem comm_ok1 : commOK CFSG.KJ4.KRS.RZT CFSG.KJ4.KRS.INV WREC (nat_lit 3) (nat_lit 11) = true := by quickRfl

theorem conj_ok : conjOK CFSG.KJ4.KRS.RZT CFSG.KJ4.KRS.INV WREC CM = true := by quickRfl

theorem f_mask : notB (conjOK CFSG.KJ4.KRS.RZT CFSG.KJ4.KRS.INV WREC
    (Nat.xor CM (Nat.shiftLeft (nat_lit 1) (nat_lit 208)))) = true := by quickRfl

theorem f_comm : notB (same CFSG.KJ4.KRS.INV (CFSG.KJ4.KRS.RZT (nat_lit 11))
    (rcat (rcat (zr CFSG.KJ4.KRS.INV WREC (nat_lit 1) (nat_lit 6)) (zr CFSG.KJ4.KRS.INV WREC (nat_lit 0) (nat_lit 6)))
      (rcat (zr CFSG.KJ4.KRS.INV WREC (nat_lit 1) (nat_lit 5)) (zr CFSG.KJ4.KRS.INV WREC (nat_lit 0) (nat_lit 5)))))
    = true := by quickRfl

theorem f_w0 : notB (wordsOK (Nat.lor WREC (nat_lit 1))) = true := by quickRfl

theorem f_shift : notB (sqOK (fun i => CFSG.KJ4.KRS.RZT (Nat.succ i)) CFSG.KJ4.KRS.INV WREC) = true := by
  quickRfl

theorem f_inv : notB (Nat.beq CFSG.KJ4.KRS.INV (nat_lit 0x5060400010203)) = true := by quickRfl

theorem f_len : notB (same CFSG.KJ4.KRS.INV (Nat.sub (CFSG.KJ4.KRS.RZT (nat_lit 0)) (nat_lit 1))
    (rcat (zr CFSG.KJ4.KRS.INV WREC (nat_lit 0) (nat_lit 5)) (zr CFSG.KJ4.KRS.INV WREC (nat_lit 0) (nat_lit 5))))
    = true := by quickRfl

end CFSG.KJ4.KShape

end
