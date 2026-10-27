module

public import Certificates.Data.CFSGNative.MonsterB.BinaryFiles
public import CFSG.Certificates.Kernel.BabyMonster.B64

public section

namespace CFSG.KC.BM.Lat

open CFSG.KC.BM CFSG.KC.BM.B64

@[expose] noncomputable def digCountN (N k : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.add ih (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (Nat.beq (Nat.sub (chAt N i) (nat_lit 48)) k)))

@[expose] noncomputable def digDefectN (N : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.add ih (Nat.sub (nat_lit 7) (Nat.sub (chAt N i) (nat_lit 48))))

@[expose] noncomputable def statsOK (N : Nat) : Bool :=
  andB (Nat.beq (digCountN N (nat_lit 0) (nat_lit 4371)) (nat_lit 0))
  (andB (Nat.beq (digCountN N (nat_lit 1) (nat_lit 4371)) (nat_lit 12))
  (andB (Nat.beq (digCountN N (nat_lit 2) (nat_lit 4371)) (nat_lit 284))
  (andB (Nat.beq (digCountN N (nat_lit 3) (nat_lit 4371)) (nat_lit 993))
  (andB (Nat.beq (digCountN N (nat_lit 4) (nat_lit 4371)) (nat_lit 1782))
  (andB (Nat.beq (digCountN N (nat_lit 5) (nat_lit 4371)) (nat_lit 1035))
  (andB (Nat.beq (digCountN N (nat_lit 6) (nat_lit 4371)) (nat_lit 243))
  (andB (Nat.beq (digCountN N (nat_lit 7) (nat_lit 4371)) (nat_lit 22))
    (Nat.beq (digDefectN N (nat_lit 4371)) (nat_lit 13123)))))))))

@[expose] noncomputable def bitAt (x i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight x i) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def zeroBits (x : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (notB (bitAt x i)))

@[expose] noncomputable def fixedBitsOK : Bool :=
  andB (bitAt CFSG.Monster.B.Binary.Native.fixedVector (nat_lit 1197))
    (zeroBits CFSG.Monster.B.Binary.Native.fixedVector (nat_lit 1197))

end CFSG.KC.BM.Lat

end
