
module

public import CFSG.Certificates.Kernel.Th.Max3S.BasicBase

public import CFSG.Certificates.Kernel.Th.Max3S.Defs
public import CFSG.Certificates.Kernel.Th.Spec.Rows
public import CFSG.Certificates.Kernel.Th.Gen.Max3

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec

section Wf

variable {A B : Array V4}

theorem wf_z (hA : WfRows A) (hB : WfRows B) : WfRows (z A B) :=
  (wfRows_wordRows (wf_x hA hB) (wf_y hA hB) _).powRows _

theorem q_eq (i : Fin 8) :
    q A B i = powRows (wordRows (x A B) (y A B) (qWord i)) (qExp i) := by
  simp [q, qs]

theorem wf_q (hA : WfRows A) (hB : WfRows B) (i : Fin 8) : WfRows (q A B i) := by
  rw [q_eq]
  exact (wfRows_wordRows (wf_x hA hB) (wf_y hA hB) _).powRows _

theorem wf_nf (hA : WfRows A) (hB : WfRows B) (s : ℕ) (e : Fin 8 → ℕ) : WfRows (nf A B s e) := by
  refine wfRows_mulRows ((wf_z hA hB).powRows s) (wfRows_prodRows fun R hR => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hR
  exact (wf_q hA hB i).powRows _

theorem nfAt_eq (k : Fin 512) :
    nfAt A B k = nf A B (k.val % 2) fun i => k.val / 2 ^ (i.val + 1) % 2 := by
  simp [nfAt, nfTab]

theorem wf_nfAt (hA : WfRows A) (hB : WfRows B) (k : Fin 512) : WfRows (nfAt A B k) := by
  rw [nfAt_eq]
  exact wf_nf hA hB _ _

theorem wf_conj (hA : WfRows A) (hB : WfRows B) (k : Fin 512) : WfRows (conj A B k) :=
  wfRows_wordRows (wf_x hA hB) (wf_y hA hB) _

theorem wf_d (hA : WfRows A) (hB : WfRows B) : WfRows (d A B) :=
  wfRows_wordRows (wf_x hA hB) (wf_y hA hB) _

theorem wf_xNf (hA : WfRows A) (hB : WfRows B) (k : Fin 512) : WfRows (xNf A B k) :=
  wfRows_mulRows (wf_x hA hB) (wf_nfAt hA hB k)

theorem wf_dNf (hA : WfRows A) (hB : WfRows B) (k : Fin 512) : WfRows (dNf A B k) :=
  wfRows_mulRows (wf_d hA hB) (wf_nfAt hA hB k)

end Wf

structure RegOK (D : CFSG.KC.Th.Gen.Max3Data) (A B : Array V4) : Prop where
  lay16 : InLayout (D.ThM3_RB 16)
  layNf : ∀ k : Fin 512, InLayout (D.ThM3_RB (25 + k.val))
  t8 : pkMat (D.ThM3_RB 5) = rowsMatrix (Max3S.t8 A B)
  s8' : pkMat (D.ThM3_RB 11) = rowsMatrix (Max3S.s8' A B)
  x : pkMat (D.ThM3_RB 13) = rowsMatrix (Max3S.x A B)
  y : pkMat (D.ThM3_RB 14) = rowsMatrix (Max3S.y A B)
  y5 : pkMat (D.ThM3_RB 15) = rowsMatrix (powRows (Max3S.y A B) 5)
  z : pkMat (D.ThM3_RB 16) = rowsMatrix (Max3S.z A B)
  q : ∀ i : Fin 8, pkMat (D.ThM3_RB (17 + i.val)) = rowsMatrix (Max3S.q A B i)
  nf : ∀ k : Fin 512, pkMat (D.ThM3_RB (25 + k.val)) = rowsMatrix (Max3S.nfAt A B k)
  d : pkMat (D.ThM3_RB 547) = rowsMatrix (Max3S.d A B)

end CFSG.KC.Th.Max3S

end
