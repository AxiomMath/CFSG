
module


public import CFSG.Certificates.Kernel.SporSch.ThRowsProved

public section

namespace CFSG.KC.Th.Spec

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.KS.SporSch.Pf
open scoped Matrix

theorem invRows_spec (X : Array CFSG.Sporadic.Th.Native.V4) (hs : X.size = 248)
    (hw : ∀ x ∈ X, x.wf = true) (hinv : ∃ Y : Matrix (Fin 248) (Fin 248) (ZMod 2),
      CFSG.Sporadic.Th.rowsMatrix X * Y = 1) :
    (CFSG.Sporadic.Th.Native.invRows X).size = 248 ∧
      (∀ r ∈ CFSG.Sporadic.Th.Native.invRows X, r.wf = true) ∧
      CFSG.Sporadic.Th.rowsMatrix X *
        CFSG.Sporadic.Th.rowsMatrix (CFSG.Sporadic.Th.Native.invRows X) = 1 ∧
      CFSG.Sporadic.Th.rowsMatrix (CFSG.Sporadic.Th.Native.invRows X) *
        CFSG.Sporadic.Th.rowsMatrix X = 1 := by
  obtain ⟨Y, hY⟩ := hinv
  have hYX : Y * rowsMatrix X = 1 := (mul_eq_one_comm (a := rowsMatrix X) (b := Y)).1 hY
  have hXinj : ∀ v, rowsMatrix X *ᵥ v = 0 → v = 0 := by
    intro v hv
    calc v = (1 : Matrix (Fin 248) (Fin 248) (ZMod 2)) *ᵥ v := (Matrix.one_mulVec v).symm
      _ = Y *ᵥ (rowsMatrix X *ᵥ v) := by rw [← hYX, Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  have hwfX : ∀ i < 248, (X[i]!).wf = true := by
    intro i hi
    have hi' : i < X.size := by rw [hs]; exact hi
    rw [getElem!_pos X i hi']
    exact hw _ (Array.getElem_mem hi')
  rw [invRows_eq_model]
  obtain ⟨⟨-, hs2, hwf, hL, -⟩, hC⟩ := fold_spec hs hwfX hXinj 248 le_rfl
  generalize (List.range' 0 248).foldl stepCol (X, idRows ()) = s at hs2 hwf hL hC ⊢
  have hone : rowsMatrix s.1 = 1 := by
    ext i j
    rw [rowsMatrix_row, toVec_bit, hC j.val j.isLt i.val i.isLt, Matrix.one_apply]
    by_cases e : i = j
    · subst e; simp
    · have e' : ¬ i.val = j.val := fun h' => e (Fin.ext h')
      simp [e, e']
  have hmul : rowsMatrix s.2 * rowsMatrix X = 1 := by rw [← hL, hone]
  refine ⟨hs2, ?_, (mul_eq_one_comm (a := rowsMatrix X) (b := rowsMatrix s.2)).2 hmul, hmul⟩
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  have hi' : i < 248 := by omega
  have := (hwf i hi').2
  rwa [getElem!_pos s.2 i hi] at this

theorem rowsMatrix_invRows_eq (X : Array CFSG.Sporadic.Th.Native.V4) (hs : X.size = 248)
    (hw : ∀ x ∈ X, x.wf = true) {Y : Matrix (Fin 248) (Fin 248) (ZMod 2)}
    (hY : CFSG.Sporadic.Th.rowsMatrix X * Y = 1) :
    CFSG.Sporadic.Th.rowsMatrix (CFSG.Sporadic.Th.Native.invRows X) = Y := by
  obtain ⟨-, -, -, h⟩ := invRows_spec X hs hw ⟨Y, hY⟩
  calc rowsMatrix (invRows X) = rowsMatrix (invRows X) * (rowsMatrix X * Y) := by
        rw [hY, Matrix.mul_one]
    _ = (rowsMatrix (invRows X) * rowsMatrix X) * Y := (Matrix.mul_assoc _ _ _).symm
    _ = Y := by rw [h, Matrix.one_mul]

end CFSG.KC.Th.Spec
