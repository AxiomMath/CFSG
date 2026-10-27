module

public import Certificates.Data.Kernel.Spor.Len

public section

namespace CFSG.KS.Len

open CFSG.KC.Enum

theorem lenFrom_eq : ∀ (cs : List Char) (k : Nat), lenFrom cs k = k + cs.length
  | [], k => rfl
  | _ :: cs, k => by
    change strictN (Nat.succ k) (lenFrom cs) = _
    have e : strictN (Nat.succ k) (lenFrom cs) = lenFrom cs (Nat.succ k) := rfl
    rw [e, lenFrom_eq cs (Nat.succ k), List.length_cons]
    omega

theorem lenK_eq (cs : List Char) : lenK cs = cs.length := by
  rw [lenK, lenFrom_eq]
  exact Nat.zero_add _

end CFSG.KS.Len

end
