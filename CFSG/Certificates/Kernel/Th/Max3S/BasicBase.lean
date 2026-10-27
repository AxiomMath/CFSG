
module

public import CFSG.Certificates.Kernel.Th.Max3S.DefsBase
public import CFSG.Certificates.Kernel.Th.Spec.RowsBase
public import CFSG.Certificates.Kernel.Th.Gen.Wrap

@[expose] public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec

section Wf

variable {A B : Array V4}

theorem wf_t3 (hA : WfRows A) (hB : WfRows B) : WfRows (t3 A B) := wfRows_mulRows hA hB

theorem wf_t4 (hA : WfRows A) (hB : WfRows B) : WfRows (t4 A B) :=
  wfRows_mulRows (wf_t3 hA hB) hB

theorem wf_t5 (hA : WfRows A) (hB : WfRows B) : WfRows (t5 A B) :=
  wfRows_mulRows (wf_t3 hA hB) (wf_t4 hA hB)

theorem wf_t6 (hA : WfRows A) (hB : WfRows B) : WfRows (t6 A B) :=
  wfRows_mulRows (wf_t3 hA hB) (wf_t5 hA hB)

theorem wf_t7 (hA : WfRows A) (hB : WfRows B) : WfRows (t7 A B) :=
  wfRows_mulRows hA (wf_t6 hA hB)

theorem wf_t8 (hA : WfRows A) (hB : WfRows B) : WfRows (t8 A B) :=
  wfRows_mulRows (wf_t6 hA hB) hA

theorem wf_u (hA : WfRows A) (hB : WfRows B) : WfRows (u A B) :=
  wfRows_mulRows ((wf_t8 hA hB).powRows 2) (wf_t7 hA hB)

theorem wf_s8 (hA : WfRows A) (hB : WfRows B) : WfRows (s8 A B) :=
  wfRows_mulRows (wf_t6 hA hB) (wf_t5 hA hB)

theorem wf_s9 (hA : WfRows A) (hB : WfRows B) : WfRows (s9 A B) :=
  wfRows_mulRows (wf_t3 hA hB) (wf_s8 hA hB)

theorem wf_s10 (hA : WfRows A) (hB : WfRows B) : WfRows (s10 A B) :=
  wfRows_mulRows (wf_s9 hA hB) (wf_t4 hA hB)

theorem wf_s7 (hA : WfRows A) (hB : WfRows B) : WfRows (s7 A B) :=
  wfRows_mulRows hA (wf_s10 hA hB)

theorem wf_s8' (hA : WfRows A) (hB : WfRows B) : WfRows (s8' A B) :=
  wfRows_mulRows (wf_s10 hA hB) hA

theorem wf_v (hA : WfRows A) (hB : WfRows B) : WfRows (v A B) :=
  wfRows_mulRows ((wf_s8' hA hB).powRows 18) (wf_s7 hA hB)

theorem wf_x (hA : WfRows A) (hB : WfRows B) : WfRows (x A B) :=
  (wf_v hA hB).powRows 14

theorem wf_y (hA : WfRows A) (hB : WfRows B) : WfRows (y A B) :=
  wfRows_mulRows (wf_t7 hA hB) ((wf_u hA hB).powRows 9)

end Wf

theorem eqRows_true_of_pk {P Q : ℕ} {X Y : Array V4} (hX : WfRows X) (hY : WfRows Y)
    (hP : pkMat P = rowsMatrix X) (hQ : pkMat Q = rowsMatrix Y) (h : P = Q) :
    eqRows X Y = true :=
  eqRows_of_rowsMatrix_eq hX hY (by rw [← hP, ← hQ, h])

theorem eqRows_false_of_pk {P Q : ℕ} {X Y : Array V4} (hPl : InLayout P) (hQl : InLayout Q)
    (hP : pkMat P = rowsMatrix X) (hQ : pkMat Q = rowsMatrix Y) (h : P ≠ Q) :
    eqRows X Y = false := by
  cases he : eqRows X Y
  · rfl
  · exact absurd (pkMat_inj hPl hQl (by rw [hP, hQ, eqRows_iff.1 he])) h

theorem eq_of_eqN {a b : ℕ} (h : CFSG.KC.Th.Gen.eqN a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem ne_of_neN {a b : ℕ} (h : CFSG.KC.Th.Gen.neN a b = true) : a ≠ b := by
  rintro rfl
  have : Nat.beq a a = true := Nat.beq_refl a
  unfold CFSG.KC.Th.Gen.neN at h
  rw [this] at h
  exact absurd h (by decide)

theorem lt_of_ltN {a b : ℕ} (h : CFSG.KC.Th.Gen.ltN a b = true) : a < b := Nat.le_of_ble_eq_true h

end CFSG.KC.Th.Max3S

end
