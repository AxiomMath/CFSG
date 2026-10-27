module

public import Certificates.Data.Kernel.SmithD6.StabN
import CFSG.Certificates.Kernel.SmithD6StabTreeSound

public section

namespace CFSG.KD.SmithD6Stab

open CFSG.KD.SmithD6ST

theorem cntGoN_eq : ∀ (l : List Nat) (a : Nat), cntGoN l a = cntGo l a
  | [], _ => rfl
  | k :: l, a => by
    change CFSG.KC.Loop.strictN (Nat.add a (Nat.pow 2 (Nat.mul 19 (clsN k)))) (cntGoN l) =
      CFSG.KC.Loop.strictN (Nat.add a (Nat.pow 2 (Nat.mul 19 (clsK k)))) (cntGo l)
    rw [clsN_eq, funext (cntGoN_eq l)]

theorem firstGoN_eq (r : Nat → Nat) : ∀ l : List Nat, firstGoN r l = firstGo r l
  | [] => rfl
  | k :: l => by
    change bAnd(Nat.ble (r (clsN k)) k, firstGoN r l) = bAnd(Nat.ble (r (clsK k)) k, firstGo r l)
    rw [clsN_eq, firstGoN_eq r l]

theorem clsChunkOKN_eq (cs : List (List Nat)) (ns : List Nat) (c : Nat) :
    clsChunkOKN cs ns c = clsChunkOK cs ns c := by
  unfold clsChunkOKN clsChunkOK
  beta_reduce
  rw [firstGoN_eq, cntGoN_eq]

end CFSG.KD.SmithD6Stab

end
