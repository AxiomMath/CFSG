module

public import Certificates.Data.Kernel.D43.Rows
public import CFSG.Certificates.Kernel.D43.MvSound

public section

namespace CFSG.KC.D43

open CFSG.ASVolI CFSG.KS CFSG.KS.ON CFSG.F3.Native CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.ON.Native

theorem rowsOK_spec {L : List Nat} {k : Nat} (h : rowsOK L k = true) :
    L.length = 84 ∧ ∀ j < 84, (burnsideF48d_rows (burnsideF48d_colTab ()) k)[j]! =
      ofV (vOf (L.getD j 0)) ∧ canon (L.getD j 0) = true := by
  simp only [rowsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact ⟨h.1.2, fun j hj => h.2 j hj⟩

theorem rows_mulVecT {L : List Nat} {k : Nat} (h : rowsOK L k = true) {X : Nat}
    (hX : VB 84 (vOf X)) :
    mulVecT (burnsideF48d_rows (burnsideF48d_colTab ()) k) (ofV (vOf X)) = ofV (vOf (mv L X)) :=
  mulVecT_mv (rowsOK_spec h).1 (rowsOK_spec h).2 hX

end CFSG.KC.D43

end
