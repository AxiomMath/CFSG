module

public import CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KS.J4Hub

open CFSG.KC.Ord CFSG.KS.Ord Matrix

@[expose] noncomputable def ordVec (p d w v : Nat) : Fin d → ZMod p :=
  fun j => ((v / 2 ^ (w * j.val) % 2 ^ w : Nat) : ZMod p)

@[expose] def RegsIn (p d w S nb L H : Nat) (G : Subgroup (GL (Fin d) (ZMod p))) (RB : Nat → Nat)
    (n : Nat) : Prop :=
  ∀ r, 0 < r → r < n → validM p nb L H (RB r) = true ∧
    ∃ g ∈ G, ((g : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) = ordMat p d w S (RB r)

@[expose] noncomputable def blkFr (BL b : Nat) : Nat := bitsN BL (Nat.mul (nat_lit 16) b) (nat_lit 8)

@[expose] noncomputable def blkTo (BL b : Nat) : Nat :=
  bitsN BL (Nat.add (Nat.mul (nat_lit 16) b) (nat_lit 8)) (nat_lit 8)

@[expose] def BlocksOK (p d w S T RM LV HV : Nat) (RB : Nat → Nat) (PR n q nbl BL : Nat) : Prop :=
  blocksOK BL nbl n = true ∧ ∀ b < nbl, ∃ PT : Nat → Nat, ∃ TC SC : List Nat, ∃ SS : Nat,
    baseFixed RB (vecR p w S d T LV HV RM) (validM p S LV HV) PR (PT 0) (blkTo BL b) n = true ∧
    Nat.beq (runTree RB PT (vecR p w S d T LV HV RM) PR (blkFr BL b) n TC 2)
      (Nat.succ (q ^ (blkTo BL b - blkFr BL b))) = true ∧
    Nat.beq (runSorted PT (q ^ (blkTo BL b - blkFr BL b)) SC 1) SS = true ∧
    sortedAll (q ^ (blkTo BL b - blkFr BL b)) SS = true

end CFSG.KS.J4Hub

end
