module

public import Certificates.Data.Kernel.M1F2
public import Certificates.Data.CFSGNative.J3.Basic
import CFSG.Certificates.Kernel.Co1F2Sound

public section

namespace CFSG.KC.M1F2

theorem j3RowsOfPayload_sound {cs : List Char} {d M : Nat} (h : m1Bind cs d M = true) :
    CFSG.Sporadic.J3.Native.rowsOfPayload d (String.ofList cs) =
      Array.ofFn (n := d) fun i => rowF d M i.val := by
  have e : CFSG.Sporadic.J3.Native.rowsOfPayload d (String.ofList cs) =
      CFSG.Sporadic.SmallF2.Native.rowsOfPayload d (String.ofList cs) := rfl
  rw [e, CFSG.KC.Co1F2.bind_sound h]
  unfold CFSG.KC.Co1F2.unpackR
  congr 1
  funext i
  unfold rowF CFSG.KLie.CT.fget CFSG.KLie.CT.maskN CFSG.KLie.CT.pw2
  change _ = (M >>> (i.val * d)) &&& ((1 <<< d) - 1)
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mul_comm]

end CFSG.KC.M1F2

end
