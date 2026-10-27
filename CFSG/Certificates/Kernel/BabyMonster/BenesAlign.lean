module

public import CFSG.Certificates.Kernel.BabyMonster.Native.Dyadic

public section

namespace CFSG.KC.BM

@[expose] noncomputable def alignedM (M : Nat) : Bool :=
  Nat.beq (Nat.mul (Nat.land M (rep (nat_lit 1) (nat_lit 16) (nat_lit 8192))) (nat_lit 65535)) M

@[expose] noncomputable def allAligned (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun M _ ih => andB (alignedM M) ih) L

@[expose] noncomputable def allAlignedL (Ls : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun L _ ih => andB (allAligned L) ih) Ls

@[expose] noncomputable def shifts16 (Ds : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun D _ ih => andB (Nat.beq (Nat.mod D (nat_lit 16)) (nat_lit 0)) ih) Ds

@[expose] noncomputable def disjFrom (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun y _ ih => andB (Nat.beq (Nat.land x y) (nat_lit 0)) ih) L

@[expose] noncomputable def pairDisj (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x t ih => andB (disjFrom x t) ih) L

@[expose] noncomputable def selDisj (Cs : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun C _ ih => andB (pairDisj (takeN (nat_lit 6) C)) ih) Cs

@[expose] def dyDs : List Nat :=
  [65536, 32768, 16384, 8192, 4096, 2048, 1024, 512, 256, 128, 64, 32, 16, 32, 64, 128, 256, 512,
    1024, 2048, 4096, 8192, 16384, 32768, 65536]

@[expose] noncomputable def netAOK (Ms Ds : List Nat) (T NM : Nat) : Bool :=
  andB (andB (allAligned Ms) (shifts16 Ds)) (benesOK Ms Ds T NM)

end CFSG.KC.BM

end
