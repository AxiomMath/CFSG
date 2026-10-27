module

import CFSG.Certificates.Kernel.Fi22LH.TreeSpec
import CFSG.Certificates.Kernel.Fi22LH.Trees
import CFSG.Certificates.Kernel.Fi22LH.RowPhi
import CFSG.Certificates.Kernel.Fi22LH.Prim
public import CFSG.Certificates.Kernel.Fi22LH.Defs
public import CFSG.Certificates.Kernel.Spor.TabWords
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.TW CFSG.KC.Enum

variable {D : LHData}

theorem far_himg (hO : OrbOK) (h : LHChecks D) :
    ∀ k < fd D.mt 80 16383, fd (D.TF k) 0 16383 < 14080 → ∀ l < 7,
      ap (phiDec D.ph)[l]! (fd (D.TF k) 0 16383) = e14 (D.ph l) (fd (D.TF k) 0 16383) ∧
        e14 (D.ph l) (fd (D.TF k) 0 16383) < 14080 :=
  fun _ _ hx l hl => ⟨(phiDec_get hl hx).2.2, (phi_facts hO h hl hx).1⟩

theorem far_bfs (hO : OrbOK) (h : LHChecks D) :
    (0 < fd D.mt 80 16383 ∧ fd D.mt 80 16383 ≤ 14080 ∧
      ∀ k < fd D.mt 80 16383, fd (D.TF k) 0 16383 < 14080) ∧
    treeBFS 14080 (fd D.mt 0 16383) (phiDec D.ph) (Array.range 7) =
      ⟨Array.ofFn (n := fd D.mt 80 16383) fun k => UInt32.ofNat (fd (D.TF k.val) 0 16383),
        Array.ofFn (n := 14080) fun x => if fd (D.QA x.val) 7792 16383 = 16383 then none32
          else UInt32.ofNat (fd (D.QA x.val) 7792 16383),
        Array.ofFn (n := fd D.mt 80 16383) fun k => UInt32.ofNat (fd (D.TF k.val) 14 16383),
        Array.ofFn (n := fd D.mt 80 16383) fun k => UInt32.ofNat (fd (D.TF k.val) 28 7)⟩ := by
  obtain ⟨h1, -, -, -, h5, h6, h7, -⟩ := farK_spec h
  exact treeBFS_eq_of (n := 14080) (root := fd D.mt 0 16383) (nl := 7) (N := fd D.mt 80 16383)
    (none := 16383) (letters := phiDec D.ph) (img := fun h l => e14 (D.ph l) (fd (D.TF h) 0 16383))
    (pts := fun k => fd (D.TF k) 0 16383) (pos := fun m => fd (D.QA m) 7792 16383)
    (par := fun k => fd (D.TF k) 14 16383) (lab := fun k => fd (D.TF k) 28 7)
    (by decide) (fd_le _ _ _) (by decide) h1 h5 (far_himg hO h) h6 h7

theorem farTree_eq (hO : OrbOK) (h : LHChecks D) :
    treeBFS 14080 (fd D.mt 0 16383) (phiDec D.ph) (Array.range xiGens.size) =
      farDec D.QA D.TF (fd D.mt 80 16383) := by
  rw [show xiGens.size = 7 from rfl, (far_bfs hO h).2]
  unfold farDec
  rw [tabDec_of_lt (f := fun k => fd (D.TF k) 0 16383) fun x _ =>
      Nat.lt_of_le_of_lt (fd_le _ _ _) (by decide),
    tabDec_of_lt (f := fun k => fd (D.TF k) 14 16383) fun x _ =>
      Nat.lt_of_le_of_lt (fd_le _ _ _) (by decide),
    tabDec_of_lt (f := fun k => fd (D.TF k) 28 7) fun x _ =>
      Nat.lt_of_le_of_lt (fd_le _ _ _) (by decide)]
  rfl

theorem c_far (hO : OrbOK) (h : LHChecks D) :
    farOK (rowInvD D) (phiDec D.ph) (fd D.mt 0 16383) (farDec D.QA D.TF (fd D.mt 80 16383)) = true := by
  obtain ⟨h1, h2, -, -, h5, h6, h7, h8⟩ := farK_spec h
  obtain ⟨⟨-, hNn, hpts⟩, he⟩ := far_bfs hO h
  have hfar := farTree_eq hO h
  rw [show xiGens.size = 7 from rfl, he] at hfar
  unfold farOK
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨decide_eq_true h1, by rw [isFar_eq h1]; exact h2⟩, ?_⟩, ?_⟩
  · rw [show xiGens.size = 7 from rfl]
    exact treeOK_of (by decide) (by decide) (fd_le _ _ _) (by decide) h1 h5 (far_himg hO h) h6 h7
      hfar.symm
  · rw [allIn_iff]
    intro m hm
    rw [isFar_eq hm, Bool.or_eq_true, Bool.not_eq_true']
    cases hfm : farB D.QA m
    · exact Or.inl rfl
    · right
      have hlt := h8 m hm hfm
      have hP2 : fd (D.TF (fd (D.QA m) 7792 16383)) 0 16383 = m := by
        unfold posK at h6
        rw [bAnd_eq, Bool.and_eq_true] at h6
        have := allN_iff.1 h6.2 m hm
        rw [strictB_eq, bIf_eq, beq_false (show fd (D.QA m) 7792 16383 ≠ 16383 by
          have := fd_le (D.QA m) 7792 16383
          omega), if_neg (by simp), bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at this
        exact this.2
      rw [← hfar]
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Array.size_ofFn]
      rw [ap_ofFn (g := fun x => if fd (D.QA x) 7792 16383 = 16383 then none32
          else UInt32.ofNat (fd (D.QA x) 7792 16383)) hm,
        if_neg (by have := fd_le (D.QA m) 7792 16383; omega), toNat_ofNat32 (by omega),
        ap_ofFn (g := fun k => UInt32.ofNat (fd (D.TF k) 0 16383)) hlt,
        toNat_ofNat32 (by have := hpts _ hlt; omega), hP2]
      exact ⟨hlt, rfl⟩

end CFSG.KS.Fi22LH
