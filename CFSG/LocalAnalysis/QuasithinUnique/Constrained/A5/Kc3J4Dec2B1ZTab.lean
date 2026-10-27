module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZTabNative
public import CFSG.Sporadic.J4.QTRankProof

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

theorem acts_of_basis (hM : MatFacts) {v : J} {T : List ℕ} (hT : lenOK T = true)
    (h : ∀ j < 11, v * eta uJ 11 (2 ^ j) * v⁻¹ = eta uJ 11 (T.getD j 0)) : Acts v T := by
  refine ⟨hT, fun c _ => ?_⟩
  have hx : ∀ j < 11, v * uJ j * v⁻¹ = eta uJ 11 (T.getD j 0) := fun j hj => by
    rw [← eta_two_pow (u := uJ) hj]
    exact h j hj
  exact conj_eta (elem_uJ hM) v (fun j => T.getD j 0) hx le_rfl c

theorem acts_of_rows (hM : MatFacts) {v : J} {M Mi : Array V2} {T : List ℕ}
    (hv : Mx v = rowsMatrix M) (hvi : Mx v⁻¹ = rowsMatrix Mi) (h : zTabOK M Mi T = true) :
    Acts v T := by
  unfold zTabOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hT, hj⟩ := h
  refine acts_of_basis hM hT fun j hj' => ?_
  apply Mx_injective
  have e := congrArg rowsMatrix (eqRows_iff.1 (hj j hj'))
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows] at e
  rw [map_mul, map_mul, hv, hvi, Mx_eta hM 11 le_rfl, Mx_eta hM 11 le_rfl]
  exact e

end CFSG.QuasithinUnique.A5
