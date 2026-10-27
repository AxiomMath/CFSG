module

public import Certificates.Data.Kernel.LaneRows
public import CFSG.Certificates.Kernel.LocalCompOps3Snd.Bridge

public section

namespace CFSG.KC.LaneRows

open CFSG.KC.LQT CFSG.KC.MiscCoset.Mat CFSG.KC.LocalComp.Ops3Snd CFSG.KS.Ord

theorem mat3_eq_matL {c : Lay} (hp : c.p = 3) {A : Nat} {X : List (List Nat)}
    (h : rowsEqK c A X = true) : mat3 c A = matL 3 c.d X := by
  ext i j
  have hi := List.all_eq_true.1 h i.val (List.mem_range.2 i.isLt)
  have hij := List.all_eq_true.1 hi j.val (List.mem_range.2 j.isLt)
  rw [hp] at hij
  simp only [mat3, ordMat, matL, Matrix.of_apply]
  exact (ZMod.natCast_eq_natCast_iff' _ _ 3).2 (Nat.eq_of_beq_eq_true hij)

end CFSG.KC.LaneRows

end
