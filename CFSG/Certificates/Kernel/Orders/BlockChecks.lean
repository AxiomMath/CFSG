module

public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KC.Ord

@[expose] noncomputable def blkBF (RB : Nat → Nat) (vm : Nat → Nat → Nat) (vldV : Nat → Bool)
    (PR BL n : Nat) (PT : Nat → Nat → Nat) (b : Nat) : Bool :=
  baseFixed RB vm vldV PR (PT b (nat_lit 0))
    (bitsN BL (Nat.add (Nat.mul (nat_lit 16) b) (nat_lit 8)) (nat_lit 8)) n

@[expose] noncomputable def blkBT (RB : Nat → Nat) (vm : Nat → Nat → Nat) (PR BL n : Nat)
    (PT : Nat → Nat → Nat) (TC : List (List Nat)) (N : List Nat) (b : Nat) : Bool :=
  Nat.beq (runTree RB (PT b) vm PR (bitsN BL (Nat.mul (nat_lit 16) b) (nat_lit 8)) n
    (TC.getD b []) (nat_lit 2)) (Nat.succ (N.getD b (nat_lit 0)))

@[expose] noncomputable def blkBS (PT : Nat → Nat → Nat) (N : List Nat) (SC : List (List Nat))
    (SS : List Nat) (b : Nat) : Bool :=
  Nat.beq (runSorted (PT b) (N.getD b (nat_lit 0)) (SC.getD b []) (nat_lit 1))
    (SS.getD b (nat_lit 0))

@[expose] noncomputable def blkBN (q BL : Nat) (N SS : List Nat) (b : Nat) : Bool :=
  andB (sortedAll (N.getD b (nat_lit 0)) (SS.getD b (nat_lit 0)))
    (Nat.beq (N.getD b (nat_lit 0)) (Nat.pow q (Nat.sub
      (bitsN BL (Nat.add (Nat.mul (nat_lit 16) b) (nat_lit 8)) (nat_lit 8))
      (bitsN BL (Nat.mul (nat_lit 16) b) (nat_lit 8)))))

end CFSG.KC.Ord

end
