module

public import CFSG.Certificates.Kernel.Local.LargeCore.Grp
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
public import CFSG.Certificates.Kernel.Orders.Mat

public section

namespace CFSG.KC.LL.HNX

open CFSG.KC.Loop CFSG.KC.LL

@[expose] noncomputable def leafA (L RB c M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight L (Nat.mul RB r)) M)
      (Nat.mul (nat_lit 1729) r))) c

@[expose] noncomputable def mulC (CM3 A G : Nat) : Nat :=
  CFSG.KC.Ord.redP (nat_lit 13) CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H (nat_lit 5) (nat_lit 9)
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.add acc (Nat.mul (Nat.land (Nat.shiftRight A (Nat.mul (nat_lit 3) k)) CM3)
        (Nat.land (Nat.shiftRight G (Nat.mul (nat_lit 1729) k)) CFSG.KD.OrdHN.RM))) (nat_lit 133))

@[expose] noncomputable def sp1 (x m s : Nat) : Nat :=
  strictN (Nat.land x m) (fun a => Nat.lor (Nat.xor x a) (Nat.shiftLeft a s))

@[expose] noncomputable def spread (MS x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun i acc => strictN acc (fun a => sp1 a (fldW MS (Nat.mul (nat_lit 1729) i) (nat_lit 1729))
      (Nat.mul (nat_lit 10) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 7) i))))) (nat_lit 8)

@[expose] noncomputable def maskB (i : Nat) : Nat :=
  (fun t => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => nIf(Nat.beq (Nat.land (Nat.shiftRight j t) (nat_lit 1)) (nat_lit 1),
      Nat.lor acc (Nat.shiftLeft (nat_lit 7) (Nat.add (Nat.mul (nat_lit 3) j)
        (Nat.mul (nat_lit 10) (Nat.shiftLeft (Nat.shiftRight j (Nat.succ t)) (Nat.succ t))))), acc))
    (nat_lit 133)) (Nat.sub (nat_lit 7) i)

@[expose] noncomputable def masksOK (MS : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight MS (Nat.mul (nat_lit 1729) (nat_lit 8))) (nat_lit 0),
    Nat.rec (motive := fun _ => Bool) true
      (fun i ih => bAnd(Nat.beq (fldW MS (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) (maskB i), ih)) (nat_lit 8))

@[expose] noncomputable def constsOK (CM3 M : Nat) : Bool :=
  bAnd(Nat.beq CM3 (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Nat.lor acc (Nat.shiftLeft (nat_lit 7) (Nat.mul (nat_lit 1729) r))) (nat_lit 64)),
    Nat.beq M (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 399)) (nat_lit 1)))

@[expose] noncomputable def edgeV (T : Nat → Nat) (RB n MS y pos t : Nat) : Nat :=
  nIf(Nat.blt t n, strictN (getRec T RB t) (fun R => strictN (fldW R (nat_lit 441) (nat_lit 22)) (fun Pt =>
      nIf(bAnd(Nat.beq y (spread MS (fldW R (nat_lit 0) (nat_lit 399))), Nat.ble Pt pos),
        nIf(Nat.beq Pt pos, nat_lit 1, nat_lit 0), nat_lit 1048576))),
    nat_lit 1048576)

@[expose] noncomputable def posOK (i P Pp : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), Nat.beq P (nat_lit 0), bAnd(Nat.ble P (Nat.mul (nat_lit 2) i), Nat.blt Pp P))

@[expose] noncomputable def coreStep (T : Nat → Nat) (RB n MS L YA YB lo r st : Nat) : Nat :=
  strictN (Nat.add lo r) (fun i => strictN (fldW L (Nat.mul RB r) RB) (fun rec =>
  strictN (fldW rec (nat_lit 441) (nat_lit 22)) (fun P =>
  strictN (Nat.shiftRight st (nat_lit 24)) (fun acc =>
  nIf(Nat.blt acc (nat_lit 1048576),
    strictN (edgeV T RB n MS (fldW YA (Nat.mul (nat_lit 1729) r) (nat_lit 1729))
        (Nat.succ (Nat.mul (nat_lit 2) i)) (fldW rec (nat_lit 399) (nat_lit 21))) (fun e0 =>
    strictN (edgeV T RB n MS (fldW YB (Nat.mul (nat_lit 1729) r) (nat_lit 1729))
        (Nat.add (Nat.mul (nat_lit 2) i) (nat_lit 2)) (fldW rec (nat_lit 420) (nat_lit 21))) (fun e1 =>
    nIf(bAnd(posOK i P (fldW st (nat_lit 0) (nat_lit 24)),
        bAnd(Nat.blt e0 (nat_lit 1048576), Nat.blt e1 (nat_lit 1048576))),
      Nat.add P (Nat.shiftLeft (Nat.add acc (Nat.add e0 e1)) (nat_lit 24)),
      Nat.shiftLeft (nat_lit 1048576) (nat_lit 24)))),
    st)))))

@[expose] noncomputable def coreInit (T : Nat → Nat) (RB lo : Nat) : Nat :=
  nIf(Nat.beq lo (nat_lit 0), nat_lit 0, fldW (getRec T RB (Nat.sub lo (nat_lit 1))) (nat_lit 441) (nat_lit 22))

@[expose] noncomputable def coreLeaf (T : Nat → Nat) (RB n MS CM3 M GA GB b c : Nat) : Nat :=
  strictN (Nat.shiftLeft b (nat_lit 6)) (fun lo => strictN (T b) (fun L =>
  strictN (leafA L RB c M) (fun A =>
  strictN (mulC CM3 A GA) (fun YA =>
  strictN (mulC CM3 A GB) (fun YB =>
  Nat.shiftRight (Nat.rec (motive := fun _ => Nat) (coreInit T RB lo)
      (fun r st => strictN st (fun s => coreStep T RB n MS L YA YB lo r s)) c) (nat_lit 24))))))

@[expose] noncomputable def sortChunk (T : Nat → Nat) (RB n SG c : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => bAnd((fun a b => bAnd(Nat.blt a n, bAnd(Nat.blt b n,
        Nat.blt (fldW (getRec T RB a) (nat_lit 0) (nat_lit 399)) (fldW (getRec T RB b) (nat_lit 0) (nat_lit 399)))))
      (fldW SG (Nat.mul (nat_lit 21) k) (nat_lit 21)) (fldW SG (Nat.mul (nat_lit 21) (Nat.succ k)) (nat_lit 21)), ih)) c

@[expose] noncomputable def auxLeaf (T U : Nat → Nat) (RB n MS CM3 M G b c : Nat) : Bool :=
  letB (T b) (fun L => letB (U b) (fun V =>
    letB (mulC CM3 (leafA L RB c M) G) (fun Y =>
    Nat.rec (motive := fun _ => Bool) true
      (fun r ih => bAnd((fun t => bAnd(Nat.blt t n,
          Nat.beq (fldW Y (Nat.mul (nat_lit 1729) r) (nat_lit 1729)) (spread MS (fldW (getRec T RB t) (nat_lit 0) (nat_lit 399)))))
        (fldW V (Nat.mul (nat_lit 21) r) (nat_lit 21)), ih)) c)))

@[expose] noncomputable def zeroRows (Y c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => Nat.add acc (nIf(Nat.beq (fldW Y (Nat.mul (nat_lit 1729) r) (nat_lit 1729)) (nat_lit 0),
      nat_lit 1, nat_lit 0))) c

@[expose] noncomputable def fixLeaf (T : Nat → Nat) (RB CM3 M : Nat) (Gs : List Nat) (b c : Nat) : Nat :=
  strictN (leafA (T b) RB c M) (fun A =>
    List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
      (fun G _ ih e => Nat.lor (Nat.shiftLeft (zeroRows (mulC CM3 A G) c) (Nat.mul (nat_lit 8) e)) (ih (Nat.succ e)))
      Gs (nat_lit 0))

@[expose] noncomputable def fixAt (T : Nat → Nat) (RB CM3 M G i : Nat) : Bool :=
  Nat.beq (mulC CM3 (Nat.land (getRec T RB i) M) G) (nat_lit 0)

@[expose] noncomputable def trM (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc (fun s => strictN (fldW a (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) (fun row =>
      Nat.rec (motive := fun _ => Nat) s
        (fun j acc2 => Nat.lor acc2 (Nat.shiftLeft (fldW row (Nat.mul (nat_lit 13) j) (nat_lit 13))
          (Nat.add (Nat.mul (nat_lit 1729) j) (Nat.mul (nat_lit 13) i)))) (nat_lit 133)))) (nat_lit 133)

end CFSG.KC.LL.HNX

end
