
module

public import CFSG.Certificates.Kernel.Th.Spec.Seed
public import CFSG.Sporadic.Th.Max3.DataBase
public import CFSG.Sporadic.ThSchreier.WordsBase

@[expose] public section

namespace CFSG.KC.Th.Spec

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier

protected theorem WfRows.mulRows {X Y : Array V4} (hX : WfRows X) (hY : WfRows Y) :
    WfRows (Native.mulRows X Y) :=
  wfRows_mulRows hX hY

theorem eqRows_eq_false_of_matrix {X Y : Array V4} (h : rowsMatrix X ≠ rowsMatrix Y) :
    eqRows X Y = false := by
  cases hb : eqRows X Y
  · rfl
  · exact absurd (rowsMatrix_eq_of_eqRows hb) h

theorem rowsMatrix_powRows (X : Array V4) : ∀ n : ℕ, rowsMatrix (powRows X n) = rowsMatrix X ^ n
  | 0 => by rw [pow_zero]; exact rowsMatrix_idRows
  | 1 => by rw [pow_one]; rfl
  | n + 2 => by
    rw [powRows, rowsMatrix_mulRows, rowsMatrix_powRows X (n + 1), pow_succ _ (n + 1)]

protected theorem WfRows.powRows {X : Array V4} (hX : WfRows X) :
    ∀ n : ℕ, WfRows (powRows X n)
  | 0 => wfRows_idRows
  | 1 => hX
  | n + 2 => (WfRows.powRows hX (n + 1)).mulRows hX

end CFSG.KC.Th.Spec

end
