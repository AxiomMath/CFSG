module

public import Certificates.Data.Kernel.J4Q.Runs
public import CFSG.Certificates.Kernel.J4Q.RepB7

public section

namespace CFSG.KC.J4Q

open CFSG.KC.LQT.T2

theorem mergeRunsK_perm (rs : List (List Nat)) : (mergeRunsK rs).Perm rs.flatten := by
  have key : ∀ n, (Nat.rec (motive := fun _ => List (List Nat)) rs
      (fun _ ih => passK ih) n).flatten.Perm rs.flatten := by
    intro n
    induction n with
    | zero => exact List.Perm.refl _
    | succ n ih => exact (passK_perm _).trans ih
  exact key 17

end CFSG.KC.J4Q

end
