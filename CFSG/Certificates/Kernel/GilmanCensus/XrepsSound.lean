module

import all Certificates.Data.Census
public import CFSG.Certificates.Kernel.GilmanCensus.ClosureSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

theorem or_bit_lt (M m k : Nat) (hk : k < M) (hm : m < 2 ^ M) : m ||| bit k < 2 ^ M := by
  rw [bit_eq]
  exact Nat.or_lt_two_pow hm (Nat.pow_lt_pow_right (by decide) hk)

theorem bitK_eq_bit (k : Nat) : bitK k = bit k := by
  rw [bit_eq, bitK, Nat.one_shiftLeft]

end Certificates.GilmanCensusK

end
