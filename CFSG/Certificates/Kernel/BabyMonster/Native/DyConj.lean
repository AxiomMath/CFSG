module

public import CFSG.Certificates.Kernel.BabyMonster.Native.DyLane
public import CFSG.Certificates.Kernel.BabyMonster.Native.F2n

public section

namespace CFSG.KC.BM

@[expose] noncomputable def cjLetter (Ms : List Nat) (NM x : Nat) : Nat :=
  Nat.xor (benes Ms lnDs x) (Nat.land NM (rep (nat_lit 8192) (nat_lit 16) (nat_lit 4371)))

@[expose] noncomputable def cjWord (Mss : List (List Nat)) (NMs : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ x => x)
    (fun Ms _ ih NMs x => List.rec (motive := fun _ => Nat) x
      (fun NM NMs' _ => forceB (cjLetter Ms NM x) (fun x' => ih NMs' x')) NMs)
    Mss NMs x

@[expose] noncomputable def cjRel (A : List (List Nat)) (a : List Nat) (B : List (List Nat)) (b : List Nat) :
    Bool :=
  Nat.beq (cjWord A a (labels (nat_lit 0) (nat_lit 8192))) (cjWord B b (labels (nat_lit 0) (nat_lit 8192)))

@[expose] noncomputable def cjBlk (R : List (List Nat)) (S : List Nat) (s : Nat) : Bool :=
  blockOKn (nat_lit 4371) (nthLL R s) (nthN S s) s

end CFSG.KC.BM

end
