module

public import CFSG.Certificates.Kernel.RouteP.MonoSet

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.RouteP

theorem memS_xor (a b N : Nat) : memS (Nat.xor a b) N = (memS a N ^^ memS b N) := by
  unfold memS
  change (a ^^^ b).testBit _ = _
  rw [Nat.testBit_xor]

theorem memS_ptsS {N : Nat} (hN : N < 920808) : memS ptsS N = true := by
  unfold memS
  have h1 : (N % 3 * 524288 + N / 3) % 524288 = N / 3 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [testBit_ptsS, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, h1]
  omega

end CFSG.KS.RouteP

end
