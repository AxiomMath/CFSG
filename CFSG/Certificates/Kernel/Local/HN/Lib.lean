module

public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
public import CFSG.Certificates.Kernel.Local.LargeCore.Grp

public section

namespace CFSG.KC.LL.HN

open CFSG.KC.Loop CFSG.KC.LL

@[expose] noncomputable def mm (a b : Nat) : Nat :=
  CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 13) (nat_lit 1729) (nat_lit 133) (nat_lit 9)
    CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.OrdHN.CM CFSG.KD.OrdHN.RM a b

@[expose] noncomputable def ln (v j : Nat) : Nat := fldW v (Nat.mul (nat_lit 13) j) (nat_lit 13)

@[expose] noncomputable def rev (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.lor acc (Nat.shiftLeft (ln v j) (Nat.mul (nat_lit 13) (Nat.sub (nat_lit 132) j)))) (nat_lit 133)

@[expose] noncomputable def cvR (a r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (Nat.mod (fldW (Nat.mul (fldW a (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) r) (nat_lit 1716) (nat_lit 13)) (nat_lit 5))
      (Nat.mul (nat_lit 13) i))) (nat_lit 133)

@[expose] noncomputable def cv (a v : Nat) : Nat := cvR a (rev v)

@[expose] noncomputable def minorX (M R C k w' S' : Nat) : Nat :=
  sumBelow (Nat.mul k k) (Nat.add (Nat.shiftRight (Nat.mul k k) (nat_lit 6)) (nat_lit 1))
    (fun t => (fun r c => Nat.shiftLeft
        (fldW M (Nat.add (Nat.mul (nat_lit 1729) (fldW R (Nat.mul (nat_lit 8) r) (nat_lit 8)))
          (Nat.mul (nat_lit 13) (fldW C (Nat.mul (nat_lit 8) c) (nat_lit 8)))) (nat_lit 13))
        (Nat.add (Nat.mul S' r) (Nat.mul w' c)))
      (Nat.div t k) (Nat.mod t k))

@[expose] noncomputable def vminor (vs : List Nat) (C k w' S' : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun v _ ih r => Nat.lor (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun c acc => Nat.lor acc (Nat.shiftLeft (ln v (fldW C (Nat.mul (nat_lit 8) c) (nat_lit 8)))
          (Nat.add (Nat.mul S' r) (Nat.mul w' c)))) k)
      (ih (Nat.succ r))) vs (nat_lit 0)

@[expose] noncomputable def subI (M : Nat) : Nat :=
  CFSG.KC.Ord.redP (nat_lit 13) CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H (nat_lit 5) (nat_lit 9)
    (Nat.add M (Nat.mul CFSG.KD.OrdHN.ONE (nat_lit 4)))

@[expose] noncomputable def fixAll (M : Nat) (vs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun v _ ih => bAnd(Nat.beq (cv M v) v, ih)) vs

@[expose] noncomputable def clsRec (P : Nat → Nat) (PRB pvb : Nat) (blk : Nat → Nat) (gs gis : List Nat)
    (pb lb db gb m n REP i : Nat) : Bool :=
  (fun RB T0 => letB (getRec blk RB i) (fun r =>
    letB (fldW r (nat_lit 0) pb) (fun x =>
    letB (fldW r pb lb) (fun L =>
    letB (fldW r (Nat.add pb lb) db) (fun d =>
    letB (fldW r (Nat.add (Nat.add pb lb) db) pb) (fun p =>
    letB (fldW r (Nat.add (Nat.add (Nat.add pb lb) db) pb) gb) (fun g =>
    (fun X => bAnd(bIf(Nat.beq i (nat_lit 0), true, Nat.blt (fldW (getRec blk RB (Nat.sub i (nat_lit 1))) (nat_lit 0) pb) x),
    bAnd(bIf(Nat.beq d (nat_lit 0), Nat.beq (fldW REP (Nat.mul pb L) pb) i,
      bAnd(Nat.blt p n, bAnd(Nat.blt g m, letB (getRec blk RB p) (fun q =>
        bAnd(Nat.beq (Nat.succ (fldW q (Nat.add pb lb) db)) d,
          bAnd(Nat.beq (fldW q pb lb) L, Nat.beq (fldW q (Nat.add T0 (Nat.mul pb g)) pb) i)))))),
    Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(ih,
      letB (fldW r (Nat.add T0 (Nat.mul pb j)) pb) (fun t =>
        bAnd(Nat.blt t n, letB (getRec blk RB t) (fun s =>
          bAnd(Nat.beq (fldW s pb lb) L,
            Nat.beq (mm (pickL gs j) (mm X (pickL gis j))) (recVal P PRB pvb (fldW s (nat_lit 0) pb)))))))) m)))
    (recVal P PRB pvb x))))))))
  (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add pb lb) db) pb) gb) (Nat.mul m pb))
  (Nat.add (Nat.add (Nat.add (Nat.add pb lb) db) pb) gb)

@[expose] noncomputable def clsRange (P : Nat → Nat) (PRB pvb : Nat) (blk : Nat → Nat) (gs gis : List Nat)
    (pb lb db gb m n REP lo c : Nat) : Bool :=
  allBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1))
    (fun j => clsRec P PRB pvb blk gs gis pb lb db gb m n REP (Nat.add lo j))

@[expose] noncomputable def ord3 (x : Nat) : Bool :=
  bAnd(Nat.beq (mm x (mm x x)) CFSG.KD.OrdHN.ONE, bIf(Nat.beq x CFSG.KD.OrdHN.ONE, false, true))

@[expose] noncomputable def clsOrd3 (P : Nat → Nat) (PRB pvb : Nat) (blk : Nat → Nat) (RB pb i : Nat) : Bool :=
  ord3 (recVal P PRB pvb (fldW (getRec blk RB i) (nat_lit 0) pb))

@[expose] noncomputable def clsOrd3At (P : Nat → Nat) (PRB pvb : Nat) (blk : Nat → Nat) (RB pb lo j : Nat) : Bool :=
  clsOrd3 P PRB pvb blk RB pb (Nat.add lo j)

@[expose] noncomputable def cvL (gs : List Nat) (j v : Nat) : Nat := cv (pickL gs j) v

end CFSG.KC.LL.HN

end
