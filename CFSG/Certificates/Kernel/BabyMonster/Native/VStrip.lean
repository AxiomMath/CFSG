module

public import CFSG.Certificates.Kernel.BabyMonster.Native.Small

public section

namespace CFSG.KC.BM

@[expose] noncomputable def commRow (Cs : List Nat) (D D' i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun C _ ih j acc => forceB
      ((fun x => Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) (nat_lit 18446744073709551616) (Nat.add acc (Nat.shiftLeft (nat_lit 1) j))
            (Nat.beq x (rowOf D' j)))
          acc (Nat.beq x (rowOf D j)))
        (rowOf C i))
      (fun acc' => forceB (Nat.succ j) (fun j' => ih j' acc'))) Cs (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def row0Strip (Ms : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun M _ ih t acc => forceB (Nat.lor acc (Nat.shiftLeft (Nat.land (nthN M (nat_lit 0)) SM) t))
      (fun a => ih (Nat.succ t) a)) Ms (nat_lit 0) (nat_lit 0)

end CFSG.KC.BM

end
