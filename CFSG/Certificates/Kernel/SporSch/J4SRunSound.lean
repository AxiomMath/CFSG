module

public import Certificates.Data.Kernel.SporSch.J4SRun
public import CFSG.Certificates.Kernel.SporSch.J4SBigSound
public import CFSG.Certificates.Kernel.J4Q.RepQT

public section

namespace CFSG.KS.SporSch.J4B

open CFSG.KC.J4Q CFSG.KC.Loop CFSG.Sporadic.GLQ CFSG.Sporadic.J4Schreier

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

private theorem eq_of_toMat {X Y : Array Nat} (hX : WfN X) (hY : WfN Y)
    (h : Sp.toMat X = Sp.toMat Y) : X = Y := by
  apply Array.ext
  · rw [hX.1, hY.1]
  · intro i h1 h2
    have hi : i < 112 := hX.1 ▸ h1
    have hx : X[i] < 2 ^ 112 := by
      have := hX.2 i hi
      rwa [getElem!_pos X i h1] at this
    have hy : Y[i] < 2 ^ 112 := by
      have := hY.2 i hi
      rwa [getElem!_pos Y i h2] at this
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 112
    · have h' := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
      change CFSG.Sporadic.SmallF2.toVecD 112 (X[i]?.getD 0) ⟨j, hj⟩ =
        CFSG.Sporadic.SmallF2.toVecD 112 (Y[i]?.getD 0) ⟨j, hj⟩ at h'
      simp only [CFSG.Sporadic.SmallF2.toVecD, getElem?_pos X i h1, getElem?_pos Y i h2,
        Option.getD_some] at h'
      cases ha : X[i].testBit j <;> cases hb : Y[i].testBit j <;> simp only [ha, hb] at h' <;>
        first | rfl | exact absurd h' (by decide)
    · have hle : 2 ^ 112 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx hle),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy hle)]

private theorem pow_wf (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) :
    ∀ (e : Nat) {X : Array Nat}, WfN X → WfN (O.pow X e) := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro X hX
    rw [CFSG.SectionRank.Native.Ops.pow]
    by_cases he : e = 0
    · rw [ite_eq_left he]
      exact (id_enc hK).1
    rw [ite_eq_right he]
    by_cases he1 : e = 1
    · rw [ite_eq_left he1]
      exact hX
    rw [ite_eq_right he1]
    have hY := ih (e / 2) (by omega) (mul_enc hK hX hX).1
    dsimp only
    split
    · exact (mul_enc hK hX hY).1
    · exact hY

theorem pow_enc (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat} (_hX : WfN X)
    (e : Nat) : WfN (O.pow X e) ∧ encN (O.pow X e) = powJ c rm one (encN X) e := by
  have hQ : ∀ e, ∃ Q, WfN Q ∧ encN Q = powJ c rm one (encN X) e ∧ Sp.toMat Q = Sp.toMat X ^ e := by
    intro e
    induction e with
    | zero =>
      refine ⟨O.one, (id_enc _hK).1, (id_enc _hK).2, ?_⟩
      rw [pow_zero]
      exact Sp.toMat_one
    | succ e ih =>
      obtain ⟨Q, hW, hE, hM⟩ := ih
      refine ⟨O.mul Q X, (mul_enc _hK hW _hX).1, ?_, ?_⟩
      · rw [(mul_enc _hK hW _hX).2, hE]
        change _ = strictN (powJ c rm one (encN X) e) (fun a => mulJ c rm a (encN X))
        rw [strictN_eq]
      · rw [Sp.toMat_mul hW.1 _hX.1, hM, pow_succ]
  obtain ⟨Q, hW, hE, hM⟩ := hQ e
  have hP := pow_wf _hK e _hX
  have he : O.pow X e = Q :=
    eq_of_toMat hP hW (by rw [(CFSG.SectionRank.OpsSpec.pow_spec Sp _hX.1 e).2, hM])
  rw [he]
  exact ⟨hW, hE⟩

@[expose] def RegOK (one : Nat) (R : Array Pair) (regs : List Nat) : Prop :=
  R.size = 9 ∧ regs.length = 18 ∧ ∀ r < 9,
    (WfN R[r]!.1 ∧ encN R[r]!.1 = getN one regs r) ∧ (WfN R[r]!.2 ∧ encN R[r]!.2 = getN one regs (9 + r))

theorem get_set {R : Array Pair} {k r : Nat} {v : Pair} (_hk : k < R.size) (hr : r < R.size) :
    (R.setIfInBounds k v)[r]! = if k = r then v else R[r]! := by
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_setIfInBounds hr, getElem!_pos R r hr]

theorem set_ok {R : Array Pair} {regs : List Nat} {k a b : Nat} {v : Pair} (h : RegOK one R regs)
    (hk : k < 9) (ha : WfN v.1 ∧ encN v.1 = a) (hb : WfN v.2 ∧ encN v.2 = b) :
    RegOK one (R.setIfInBounds k v) (setN (setN regs k a) (9 + k) b) := by
  obtain ⟨hs, hl, hR⟩ := h
  refine ⟨by simp [hs], by rw [length_setN, length_setN, hl], fun r hr => ?_⟩
  rw [get_set (by omega) (by omega)]
  have l1 : k < (setN regs k a).length := by rw [length_setN]; omega
  have g1 : getN one (setN (setN regs k a) (9 + k) b) r = if r = k then a else getN one regs r := by
    rw [getN_setN _ _ _ _ _ (by rw [length_setN]; omega), ite_eq_right (by omega), getN_setN _ _ _ _ _ (by omega)]
  have g2 : getN one (setN (setN regs k a) (9 + k) b) (9 + r) =
      if r = k then b else getN one regs (9 + r) := by
    rw [getN_setN _ _ _ _ _ (by rw [length_setN]; omega)]
    by_cases h : r = k
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h, getN_setN _ _ _ _ _ (by omega), ite_eq_right (by omega)]
  rw [g1, g2]
  by_cases h : k = r
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl]
    exact ⟨ha, hb⟩
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), ite_eq_right (Ne.symm h)]
    exact hR r hr

variable (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
include hK

theorem step_ok {R : Array Pair} {regs : List Nat} (h : RegOK one R regs) {ins : Instr}
    (hi : ins.lt 9 = true) : RegOK one (Instr.runN O R ins) (stepPK c rm one regs ins) := by
  have hR := h.2.2
  cases ins with
  | mu i j k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨hi, hj⟩, hk⟩ := hi
    rw [Instr.runN, stepPK]
    simp only [strictL_eq]
    refine set_ok h hk ?_ ?_
    · have m := mul_enc hK (hR i hi).1.1 (hR j hj).1.1
      exact ⟨m.1, by rw [m.2, (hR i hi).1.2, (hR j hj).1.2]⟩
    · have m := mul_enc hK (hR j hj).2.1 (hR i hi).2.1
      exact ⟨m.1, by rw [m.2, (hR i hi).2.2, (hR j hj).2.2]; rfl⟩
  | iv i k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨hi, hk⟩ := hi
    rw [Instr.runN, stepPK]
    simp only [strictL_eq]
    exact set_ok h hk ⟨(hR i hi).2.1, (hR i hi).2.2⟩ ⟨(hR i hi).1.1, (hR i hi).1.2⟩
  | pwr e i k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨hi, hk⟩ := hi
    rw [Instr.runN, stepPK]
    simp only [strictL_eq]
    refine set_ok h hk ?_ ?_
    · have m := pow_enc hK (hR i hi).1.1 e
      exact ⟨m.1, by rw [m.2, (hR i hi).1.2]⟩
    · have m := pow_enc hK (hR i hi).2.1 e
      exact ⟨m.1, by rw [m.2, (hR i hi).2.2]; rfl⟩

theorem runPK_ok : ∀ (p : List Instr) {R : Array Pair} {regs : List Nat}, RegOK one R regs →
    (∀ ins ∈ p, ins.lt 9 = true) → RegOK one (runProgN O R p) (runPK c rm one regs p)
  | [], _, _, h, _ => h
  | ins :: p, R, regs, h, hp => by
    have h1 := step_ok hK h (hp ins List.mem_cons_self)
    have := runPK_ok p h1 fun i hi => hp i (List.mem_cons_of_mem _ hi)
    rw [runProgN, List.foldl_cons]
    exact this

end CFSG.KS.SporSch.J4B

end
