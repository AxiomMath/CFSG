module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Certificate28041
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint

section Regs

variable {M V : Type} [Inhabited M] {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
  (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p)))

@[expose] def RegsOK' (R : Array M) : Prop := ∀ r < R.size, Sp.WF R[r]! ∧ Sp.toMat R[r]! ∈ S

omit Sp in
theorem getElem!_setIfInBounds_of_lt' {R : Array M} {k r : ℕ} (hr : r < R.size) (x : M) :
    (R.setIfInBounds k x)[r]! = if k = r then x else R[r]! := by
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_setIfInBounds,
    getElem!_pos R r hr]

theorem step_ok' {R : Array M} (hR : RegsOK' Sp S R) {op : Op} (hop : op.lt R.size = true) :
    (O.step R op).size = R.size ∧ RegsOK' Sp S (O.step R op) := by
  cases op with
  | mul i j k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨⟨hi, hj⟩, hk⟩ := hop
    have hs : (O.step R (.mul i j k)).size = R.size := by
      simp [Ops.step, Array.set!]
    refine ⟨hs, fun r hr => ?_⟩
    rw [hs] at hr
    simp only [Ops.step, Array.set!]
    rw [getElem!_setIfInBounds_of_lt' hr]
    split
    · obtain ⟨wi, mi⟩ := hR i hi
      obtain ⟨wj, mj⟩ := hR j hj
      exact ⟨Sp.mul_wf wi wj, by rw [Sp.toMat_mul wi wj]; exact S.mul_mem mi mj⟩
    · exact hR r hr
  | pow e i k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨hi, hk⟩ := hop
    have hs : (O.step R (.pow e i k)).size = R.size := by
      simp [Ops.step, Array.set!]
    refine ⟨hs, fun r hr => ?_⟩
    rw [hs] at hr
    simp only [Ops.step, Array.set!]
    rw [getElem!_setIfInBounds_of_lt' hr]
    split
    · obtain ⟨wi, mi⟩ := hR i hi
      obtain ⟨w, m⟩ := Sp.pow_spec wi e
      exact ⟨w, by rw [m]; exact S.pow_mem mi e⟩
    · exact hR r hr

theorem run_ok' (prog : List Op) {R : Array M} (hR : RegsOK' Sp S R)
    (hprog : prog.all (Op.lt R.size) = true) :
    (O.run prog R).size = R.size ∧ RegsOK' Sp S (O.run prog R) := by
  induction prog generalizing R with
  | nil => exact ⟨rfl, hR⟩
  | cons op prog ih =>
    rw [List.all_cons, Bool.and_eq_true] at hprog
    obtain ⟨hs, hok⟩ := step_ok' Sp S hR hprog.1
    have := ih hok (by rw [hs]; exact hprog.2)
    simp only [Ops.run, List.foldl_cons] at this ⊢
    rw [this.1, hs]
    exact ⟨rfl, this.2⟩

theorem initRegs_ok' {A B : M} (hA : Sp.WF A ∧ Sp.toMat A ∈ S) (hB : Sp.WF B ∧ Sp.toMat B ∈ S)
    (n : ℕ) : (O.initRegs A B n).size = n ∧ RegsOK' Sp S (O.initRegs A B n) := by
  have hs : (O.initRegs A B n).size = n := by simp [Ops.initRegs]
  refine ⟨hs, fun r hr => ?_⟩
  rw [hs] at hr
  unfold Ops.initRegs
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
  split
  · exact hA
  split
  · exact hB
  · exact ⟨Sp.one_wf, by rw [Sp.toMat_one]; exact S.one_mem⟩

end Regs

theorem exists_unit_order_eight_of_ord8OK {M V : Type} [Inhabited M] {O : Ops M V} {p d : ℕ}
    (Sp : OpsSpec O p d) (D : Data) (r k : ℕ) (h : ord8OK O D r k = true) :
    ∃ x : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ, x ^ 8 = 1 ∧ x ^ 4 ≠ 1 := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  unfold ord8OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hn, hprog⟩, hr⟩, h8⟩, hne⟩ := h
  have hA : Sp.WF (O.decode D.seedA) ∧ Sp.toMat (O.decode D.seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.seedB) ∧ Sp.toMat (O.decode D.seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  obtain ⟨hs0, hok0⟩ := initRegs_ok' Sp S hA hB D.nregs
  obtain ⟨hs, hok⟩ := run_ok' Sp S D.prog hok0 (by rw [hs0]; exact hprog)
  set R := O.run D.prog (O.initRegs (O.decode D.seedA) (O.decode D.seedB) D.nregs) with hR
  rw [hs0] at hs
  obtain ⟨wX, mX⟩ := hok r (by rw [hs]; exact hr)
  obtain ⟨w8, m8⟩ := Sp.pow_spec wX 8
  obtain ⟨w4, m4⟩ := Sp.pow_spec wX 4
  have h8' : Sp.toMat R[r]! ^ 8 = 1 := by
    have := Sp.toMat_eq w8 Sp.one_wf h8
    rwa [m8, Sp.toMat_one] at this
  have h4' : Sp.toMat R[r]! ^ 4 ≠ 1 := by
    intro h4
    apply Sp.toVec_ne hne
    rw [Sp.toVec_vmul (Sp.unit_wf k) w4, m4, h4, Matrix.vecMul_one]
  have hS8 : (⟨Sp.toMat R[r]!, mX⟩ : S) ^ 8 = 1 := Subtype.ext (by simpa using h8')
  let u : Sˣ := Units.ofPowEqOne _ 8 hS8 (by norm_num)
  refine ⟨u, Units.pow_ofPowEqOne _ _, fun h4 => h4' ?_⟩
  have := congrArg (fun v : Sˣ => ((v : S) : Matrix (Fin d) (Fin d) (ZMod p))) h4
  simpa [u] using this

theorem exists_order_eight_Th :
    ∃ x : CFSG.Blueprint.NativeSporadic.Th, x ^ 8 = 1 ∧ x ^ 4 ≠ 1 :=
  exists_unit_order_eight_of_ord8OK (spec2 248) thOrd8Data 11 0
    Certificates.certificate28041

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
