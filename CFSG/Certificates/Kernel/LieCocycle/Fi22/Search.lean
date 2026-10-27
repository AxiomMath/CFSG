module

public import CFSG.Certificates.Kernel.LieCocycle.Fi22.Core

public section

namespace CFSG.KLC.Fi22

open CFSG.KC.Loop

@[expose] noncomputable def invoOk (A n : Nat) : Bool :=
  fsplit (nat_lit 1024) (nat_lit 6) A (fun FA =>
    allLt n (fun i => andB (Nat.blt (ent FA i) n) (Nat.beq (ent FA (ent FA i)) i)))

@[expose] noncomputable def commOk (A B n : Nat) : Bool :=
  fsplit (nat_lit 1024) (nat_lit 6) A (fun FA => fsplit (nat_lit 1024) (nat_lit 6) B (fun FB =>
    allLt n (fun i => Nat.beq (ent FA (ent FB i)) (ent FB (ent FA i)))))

@[expose] noncomputable def row0Of (FZ : Nat → Nat) (n : Nat) : Nat :=
  Nat.shiftRight (iterN (Nat.sub n (nat_lit 1)) (fun i acc => (fun j =>
      Nat.lor (Nat.lor (Nat.xor acc (Nat.land acc (nat_lit 65535)))
          (Nat.mul (Nat.shiftLeft (nat_lit 1) (Nat.add j (nat_lit 16)))
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq (ent FZ j) j))))
        j) (Nat.add i (nat_lit 1))) (nat_lit 0)) (nat_lit 16)

@[expose] noncomputable def graphOk (Z MB n : Nat) : Bool :=
  fsplit (nat_lit 1024) (nat_lit 6) Z (fun FZ =>
    fsplit (nat_lit 65536) (nat_lit 8) MB (fun FM =>
      sB (row0Of FZ n) (fun r0 =>
        andB (Nat.beq (rowAt FM (nat_lit 0)) r0)
          (andB (Nat.beq (sumBelow n (Nat.add (Nat.shiftRight n (nat_lit 6)) (nat_lit 1)) (fun j =>
              Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (bt r0 j))) (nat_lit 693))
            (allLt n (fun j => orB (notB (bt r0 j)) (bt (rowAt FM j) (nat_lit 0))))))))

@[expose] noncomputable def realizesInv (FP FG : Nat → Nat) (n : Nat) : Bool :=
  allLt n (fun p => andB (Nat.blt (ent FP p) n) (Nat.beq (ent FG (ent FP p)) p))

@[expose] noncomputable def rowsMatch (FZ FM FG : Nat → Nat) (n : Nat) : Bool :=
  allLt n (fun i => Nat.beq (rowAt FZ i) (rowAt FM (ent FG i)))

@[expose] noncomputable def presOk (GA NW MB n : Nat) : Bool :=
  fsplit (nat_lit 1024) (nat_lit 6) GA (fun FG =>
    fsplit (nat_lit 1024) (nat_lit 6) (arrNW NW) (fun FP =>
      andB (realizesInv FP FG n)
        (sB REP (fun R =>
          fsplit (nat_lit 65536) (nat_lit 8) MB (fun FM =>
            fsplit (nat_lit 65536) (nat_lit 8) (applyNW NW R MB) (fun FZ => rowsMatch FZ FM FG n))))))

@[expose] noncomputable def leafOk (n MB TA NWs NWk ACC : Nat) : Bool :=
  fsplit (nat_lit 1024) (nat_lit 6) (arrNW NWk) (fun FK =>
    fsplit (nat_lit 1024) (nat_lit 6) (arrInvNW NWs) (fun FSI =>
      fsplit (nat_lit 1024) (nat_lit 6) ACC (fun FA =>
        fsplit (nat_lit 1024) (nat_lit 6) TA (fun FT =>
          andB (allLt n (fun v => andB (Nat.beq (ent FA v) (ent FK (ent FSI v)))
              (Nat.beq (ent FA (ent FT v)) (ent FT (ent FA v)))))
            (sB REP (fun R =>
              fsplit (nat_lit 65536) (nat_lit 8) MB (fun FM =>
                fsplit (nat_lit 65536) (nat_lit 8) (applyInvNW NWk R (applyNW NWs R MB)) (fun FZ =>
                  rowsMatch FZ FM FA n))))))))

@[expose] noncomputable def leafFailOk (n MB TA NWs NWk kind x y : Nat) : Bool :=
  fsplit (nat_lit 1024) (nat_lit 6) (arrNW NWk) (fun FK =>
    fsplit (nat_lit 1024) (nat_lit 6) (arrInvNW NWs) (fun FSI =>
      andB (andB (Nat.blt x n) (Nat.blt y n))
        (Bool.rec (motive := fun _ => Bool)
          (notB (Nat.beq (ent FK (ent FSI (fw TA (nat_lit 16) x))) (fw TA (nat_lit 16) (ent FK (ent FSI x)))))
          (andB (bt (fw MB (nat_lit 4096) x) y)
            (notB (bt (fw MB (nat_lit 4096) (ent FK (ent FSI x))) (ent FK (ent FSI y)))))
          (Nat.beq kind (nat_lit 1)))))

@[expose] noncomputable def oePt (o : Nat) : Nat := Nat.land o (nat_lit 4095)
@[expose] noncomputable def oePar (o : Nat) : Nat := Nat.land (Nat.shiftRight o (nat_lit 12)) (nat_lit 4095)
@[expose] noncomputable def oeSlot (o : Nat) : Nat := Nat.land (Nat.shiftRight o (nat_lit 24)) (nat_lit 255)

@[expose] noncomputable def chRep (h : Nat) : Nat := Nat.land h (nat_lit 4095)
@[expose] noncomputable def chSize (h : Nat) : Nat := Nat.land (Nat.shiftRight h (nat_lit 12)) (nat_lit 4095)
@[expose] noncomputable def chStart (h : Nat) : Nat := Nat.shiftRight h (nat_lit 24)

@[expose] noncomputable def prefixFixed (PL : Nat → Nat) (PFX d ng IX : Nat) : Bool :=
  allLt ng (fun j => allLt d (fun i =>
    Nat.beq (fw (PL (fw IX (nat_lit 8) j)) (nat_lit 16) (fw PFX (nat_lit 12) i)) (fw PFX (nat_lit 12) i)))

@[expose] noncomputable def entryOk (PL : Nat → Nat) (OE IX ng c e i acc o ps : Nat) : Bool :=
  andB (Nat.ble c ps) (andB (Nat.blt ps e) (andB (notB (bt acc (Nat.add ps (nat_lit 16))))
    (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (oePar o) i) (andB (Nat.blt (oeSlot o) ng)
        (Nat.beq (fw (PL (fw IX (nat_lit 8) (oeSlot o))) (nat_lit 16) (oePt (fw OE (nat_lit 40) (oePar o)))) (oePt o))))
      true (bt o (nat_lit 32)))))

@[expose] noncomputable def entriesOk (PL FKI : Nat → Nat) (OE IX ng c e ne : Nat) : Bool :=
  sB (iterN ne (fun i acc =>
      sN (fw OE (nat_lit 40) i) (fun o => sN (ent FKI (oePt o)) (fun ps =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (Nat.lor (Nat.lor (Nat.xor acc (Nat.land acc (nat_lit 65535))) (Nat.shiftLeft (nat_lit 1) (Nat.add ps (nat_lit 16))))
            (Nat.add i (nat_lit 1)))
          (andB (Nat.blt (nat_lit 0) acc) (entryOk PL OE IX ng c e i acc o ps)))))
    (Nat.shiftLeft (nat_lit 1) (nat_lit 4112))) (fun acc => Nat.blt (nat_lit 0) acc)

@[expose] noncomputable def childrenOk (OE CHD nch ne : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) nch)
    (andB (Nat.beq (chStart (fw CHD (nat_lit 36) (nat_lit 0))) (nat_lit 0))
      (andB (Nat.beq (Nat.add (chStart (fw CHD (nat_lit 36) (Nat.sub nch (nat_lit 1))))
          (chSize (fw CHD (nat_lit 36) (Nat.sub nch (nat_lit 1))))) ne)
        (allLt nch (fun j => sB (fw CHD (nat_lit 36) j) (fun h =>
          sB (fw OE (nat_lit 40) (chStart h)) (fun o =>
            andB (andB (bt o (nat_lit 32)) (Nat.beq (oePt o) (chRep h)))
              (andB (Nat.blt (nat_lit 0) (chSize h))
                (andB (orB (Nat.beq j (Nat.sub nch (nat_lit 1)))
                    (Nat.beq (Nat.add (chStart h) (chSize h)) (chStart (fw CHD (nat_lit 36) (Nat.add j (nat_lit 1))))))
                  (allLt (chSize h) (fun i => orB (Nat.beq i (nat_lit 0))
                    (notB (bt (fw OE (nat_lit 40) (Nat.add (chStart h) i)) (nat_lit 32)))))))))))))

@[expose] noncomputable def branchOk (PL : Nat → Nat) (n NWk SFk NWs SFs v qs c e d PFX ng IX ne OE nch CHD : Nat) :
    Bool :=
  andB (Nat.beq SFk SFs) (andB (isCell SFs n c e) (andB (Nat.ble c qs) (andB (Nat.blt qs e)
    (andB (Nat.beq ne (Nat.sub e c)) (andB (prefixFixed PL PFX d ng IX) (andB (childrenOk OE CHD nch ne)
      (fsplit (nat_lit 1024) (nat_lit 6) (arrNW NWs) (fun FS =>
        fsplit (nat_lit 1024) (nat_lit 6) (arrInvNW NWk) (fun FKI =>
          andB (Nat.beq (ent FS qs) v) (entriesOk PL FKI OE IX ng c e ne))))))))))

end CFSG.KLC.Fi22

end
