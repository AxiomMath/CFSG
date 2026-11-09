module

public import CFSG.Certificates.Kernel.F3PlanesLay
public import CFSG.Certificates.Kernel.J4Hub.RegSound
public import CFSG.F3.Spec
public import Certificates.Data.Kernel.OpsLayFillOne

public section

namespace CFSG.F3.Planes

open CFSG.KC.LQT CFSG.KC.Ord CFSG.KS.Ord CFSG.F3.Native

@[expose] noncomputable def fp3PlOK (N p m : Nat) : Bool :=
  Nat.blt p (Nat.shiftLeft 1 N) && Nat.blt m (Nat.shiftLeft 1 N) && Nat.beq (Nat.land p m) 0

@[expose] noncomputable def fp3MulK (c : Lay) (N L X Y Z : Nat) : Bool :=
  fp3ToPK c.w N L X fun Xp Xm => fp3ToPK c.w N L Y fun Yp Ym =>
  fp3LoopK c.d (fp3RepN c.d c.d) (Nat.sub (Nat.shiftLeft 1 c.d) 1) Xp Xm Yp Ym c.d 0 0
    fun Zp Zm =>
  fp3OfPK c.w N L Zp Zm fun Z' => fp3OfPK c.w N L Xp Xm fun X' => fp3OfPK c.w N L Yp Ym fun Y' =>
  Nat.beq Z' Z && Nat.beq X' X && Nat.beq Y' Y && fp3PlOK N Xp Xm && fp3PlOK N Yp Ym &&
    fp3PlOK N Zp Zm && validM c.p (Nat.mul c.d c.S) c.L c.H X &&
    validM c.p (Nat.mul c.d c.S) c.L c.H Y && validM c.p (Nat.mul c.d c.S) c.L c.H Z

theorem fp3Geo_succ (P : Nat) : ∀ n, fp3Geo P (n + 1) = fp3Geo P n * 2 ^ P + 1
  | 0 => by simp [fp3Geo]
  | n + 1 => by
    have h1 : fp3Geo P (n + 2) = fp3Geo P (n + 1) + 2 ^ (P * (n + 1)) := rfl
    have h2 : fp3Geo P (n + 1) = fp3Geo P n + 2 ^ (P * n) := rfl
    rw [h1]
    conv_rhs => rw [h2]
    rw [fp3Geo_succ P n, Nat.add_mul, Nat.mul_succ, Nat.pow_add]
    omega

theorem fp3Rep_eq (d : Nat) : ∀ n, fp3Rep d n = fp3Geo d n
  | 0 => rfl
  | n + 1 => by rw [fp3Rep, fp3Rep_eq d n, fp3Geo_succ]

theorem fp3Lane_bit {w N p m y : Nat} (hw : 2 ≤ w) (hy : ∀ j, y.testBit j =
      (decide (j % w < 2) && decide (j / w < N) && fp3PB p m (j / w) (j % w)))
    {t : Nat} (ht : t < N) (b : Nat) :
    (y / 2 ^ (w * t) % 2 ^ w).testBit b = (decide (b < 2) && fp3PB p m t b) := by
  rw [Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight, hy]
  by_cases hb : b < w
  · have e1 : (w * t + b) % w = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
    have e2 : (w * t + b) / w = t := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hb, Nat.zero_add]
    rw [e1, e2]
    simp [hb, ht]
  · rw [decide_eq_false hb, decide_eq_false (by omega : ¬ b < 2)]
    simp

theorem fp3Lane_val {w N p m y : Nat} (hw : 2 ≤ w) (hy : ∀ j, y.testBit j =
      (decide (j % w < 2) && decide (j / w < N) && fp3PB p m (j / w) (j % w)))
    {t : Nat} (ht : t < N) (hpm : (p.testBit t && m.testBit t) = false) :
    ((y / 2 ^ (w * t) % 2 ^ w : Nat) : ZMod 3) = bitVal (p.testBit t) (m.testBit t) := by
  have h2 : ∀ b, (2 : Nat).testBit (b + 2) = false := fun b =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have h1 : ∀ b, (1 : Nat).testBit (b + 2) = false := fun b =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) (by omega)))
  cases hp : p.testBit t <;> cases hm : m.testBit t
  · have k : y / 2 ^ (w * t) % 2 ^ w = 0 := Nat.eq_of_testBit_eq fun b => by
      rw [fp3Lane_bit hw hy ht]
      rcases b with _ | _ | b <;> simp [fp3PB, hp, hm]
    rw [k]
    simp [bitVal]
  · have k : y / 2 ^ (w * t) % 2 ^ w = 2 := Nat.eq_of_testBit_eq fun b => by
      rw [fp3Lane_bit hw hy ht]
      rcases b with _ | _ | b <;> simp [fp3PB, hp, hm, h2, (by decide : Nat.testBit 2 1 = true)]
    rw [k]
    simp [bitVal]
  · have k : y / 2 ^ (w * t) % 2 ^ w = 1 := Nat.eq_of_testBit_eq fun b => by
      rw [fp3Lane_bit hw hy ht]
      rcases b with _ | _ | b <;> simp [fp3PB, hp, hm, h1, (by decide : Nat.testBit 1 1 = false)]
    rw [k]
    simp [bitVal]
  · simp [hp, hm] at hpm

theorem fp3OrdMat {d w p m y : Nat} (hw : 2 ≤ w) (hy : ∀ j, y.testBit j =
      (decide (j % w < 2) && decide (j / w < d * d) && fp3PB p m (j / w) (j % w)))
    (hpm : p &&& m = 0) :
    ordMat 3 d w (d * w) y = toMat d (fp3Rows d ⟨p, m⟩) := by
  ext i j
  have ht : i.val * d + j.val < d * d := by
    have := Nat.mul_le_mul_right d (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    have := j.isLt
    rw [Nat.mul_comm d d]
    omega
  have hb : (p.testBit (i.val * d + j.val) && m.testBit (i.val * d + j.val)) = false := by
    rw [← Nat.testBit_and, hpm, Nat.zero_testBit]
  have e : d * w * i.val + w * j.val = w * (i.val * d + j.val) := by
    rw [Nat.mul_add, Nat.mul_comm d w, Nat.mul_assoc, Nat.mul_comm d i.val]
  unfold ordMat
  rw [toMat_apply, e, fp3Lane_val hw hy ht hb, fp3Rows,
    getElem!_pos (Array.ofFn _) i.val (by simp), Array.getElem_ofFn, V.val_eq_bitVal]
  simp only [fp3Row, testBit_fp3Blk, j.isLt, decide_true, Bool.true_and]

theorem fp3Rows_wf {d p m : Nat} (hpm : p &&& m = 0) : RowsWF (fp3Rows d ⟨p, m⟩) := by
  intro i
  by_cases hi : i < d
  · rw [fp3Rows, getElem!_pos (Array.ofFn _) i (by simpa using hi), Array.getElem_ofFn]
    simp only [V.wf, fp3Row, beq_iff_eq]
    rw [← fp3Blk_and, hpm, fp3Blk_zero]
  · rw [getElem!_neg _ i (by simpa [fp3Rows] using hi)]
    rfl

theorem fp3PlOK_spec {N p m : Nat} (h : fp3PlOK N p m = true) :
    p < 2 ^ N ∧ m < 2 ^ N ∧ p &&& m = 0 := by
  have e : Nat.shiftLeft 1 N = 2 ^ N := by
    change 1 <<< N = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  simp only [fp3PlOK, Bool.and_eq_true, Nat.blt_eq, e] at h
  exact ⟨h.1.1, h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem fp3MulK_sound {c : Lay} (hc : c.ok = true) (hp : c.p = 3) (hS : c.S = c.d * c.w)
    (hd : 0 < c.d) (hw : 2 ≤ c.w) {N L X Y Z : Nat} (hN : N = c.d * c.d) (hL : N ≤ 2 ^ L)
    (h : fp3MulK c N L X Y Z = true) : CFSG.KC.OpsLayK.mulEq c X Y Z = true := by
  have hc' : constsOK c.p c.w c.S c.d c.T c.L c.H c.CM c.RM c.ONE c.LV c.HV = true := hc
  obtain ⟨Xp, Xm, eX⟩ := fp3ToPK_ex c.w N L X
  obtain ⟨Yp, Ym, eY⟩ := fp3ToPK_ex c.w N L Y
  have eR : fp3RepN c.d c.d = fp3Rep c.d c.d := by rw [fp3RepN_eq hd, fp3Rep_eq]
  have eT : Nat.sub (Nat.shiftLeft 1 c.d) 1 = 2 ^ c.d - 1 := by
    change 1 <<< c.d - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  let PZ := fp3Mul c.d ⟨Xp, Xm⟩ ⟨Yp, Ym⟩
  obtain ⟨Z', eZ, hZ⟩ := fp3OfPK_eq hw hL PZ.p PZ.m
  obtain ⟨X', eX', hX'⟩ := fp3OfPK_eq hw hL Xp Xm
  obtain ⟨Y', eY', hY'⟩ := fp3OfPK_eq hw hL Yp Ym
  unfold fp3MulK at h
  rw [eX, eY, eR, eT, fp3LoopK_fp3Mul c.d ⟨Xp, Xm⟩ ⟨Yp, Ym⟩, eZ, eX', eY'] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, hx⟩, hy⟩, pX⟩, pY⟩, pZ⟩, vX⟩, vY⟩, vZ⟩ := h
  obtain ⟨xp, xm, xpm⟩ := fp3PlOK_spec pX
  obtain ⟨yp, ym, ypm⟩ := fp3PlOK_spec pY
  obtain ⟨zp, zm, zpm⟩ := fp3PlOK_spec pZ
  obtain rfl := Nat.eq_of_beq_eq_true hz
  obtain rfl := Nat.eq_of_beq_eq_true hx
  obtain rfl := Nat.eq_of_beq_eq_true hy
  subst hN
  have hnb : Nat.mul c.d c.S = c.d * c.S := rfl
  obtain ⟨vXY, mXY⟩ := CFSG.KS.J4Hub.mul_sound' hc' hnb vX vY
  have mX := fp3OrdMat (d := c.d) hw (hX' xp xm) xpm
  have mY := fp3OrdMat (d := c.d) hw (hY' yp ym) ypm
  have mZ := fp3OrdMat (d := c.d) hw (hZ zp zm) zpm
  have hwX : ∀ i < c.d, (fp3Row c.d ⟨Xp, Xm⟩ i).wf = true := fun i hi => by
    have := fp3Rows_wf (d := c.d) xpm i
    rwa [fp3Rows, getElem!_pos (Array.ofFn _) i (by simpa using hi), Array.getElem_ofFn] at this
  have eZm : ordMat 3 c.d c.w (c.d * c.w) Z' =
      ordMat 3 c.d c.w (c.d * c.w) X' * ordMat 3 c.d c.w (c.d * c.w) Y' := by
    rw [mZ, mX, mY]
    change toMat c.d (fp3Rows c.d (fp3Mul c.d ⟨Xp, Xm⟩ ⟨Yp, Ym⟩)) = _
    rw [fp3Rows_fp3Mul hd hwX, toMat_mul (by simp [fp3Rows]) (fp3Rows_wf xpm) (fp3Rows_wf ypm)]
  rw [← hS] at eZm
  rw [hp] at mXY
  have e2 : c.mul X' Y' = Z' := CFSG.KS.J4Hub.ordMat_inj' hc' hnb vXY vZ (by
    unfold Lay.mul
    rw [hp, mXY, eZm])
  unfold CFSG.KC.OpsLayK.mulEq
  rw [e2]
  exact Nat.beq_refl Z'

@[expose] noncomputable def fp3MulOK (c : Lay) (N L X Y Z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (fp3MulK c N L X Y Z)
    (Nat.beq X Z && validM c.p (Nat.mul c.d c.S) c.L c.H X) (Nat.beq Y c.ONE)

theorem fp3MulOK_sound {c : Lay} (hc : c.ok = true) (hp : c.p = 3) (hS : c.S = c.d * c.w)
    (hd : 0 < c.d) (hw : 2 ≤ c.w) {N L X Y Z : Nat} (hN : N = c.d * c.d) (hL : N ≤ 2 ^ L)
    (h : fp3MulOK c N L X Y Z = true) : CFSG.KC.OpsLayK.mulEq c X Y Z = true := by
  unfold fp3MulOK at h
  cases hY : Nat.beq Y c.ONE
  · rw [hY] at h
    exact fp3MulK_sound hc hp hS hd hw hN hL h
  · rw [hY] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hz, vX⟩ := h
    obtain rfl := Nat.eq_of_beq_eq_true hY
    obtain rfl := Nat.eq_of_beq_eq_true hz
    have hc' : constsOK c.p c.w c.S c.d c.T c.L c.H c.CM c.RM c.ONE c.LV c.HV = true := hc
    have hnb : Nat.mul c.d c.S = c.d * c.S := rfl
    obtain ⟨vO, mO⟩ := CFSG.KS.J4Hub.one_sound' hc' hnb
    obtain ⟨vXO, mXO⟩ := CFSG.KS.J4Hub.mul_sound' hc' hnb vX vO
    have e2 : c.mul X c.ONE = X := by
      unfold Lay.mul
      exact CFSG.KS.J4Hub.ordMat_inj' hc' hnb vXO vX (by rw [mXO, mO, Matrix.mul_one])
    unfold CFSG.KC.OpsLayK.mulEq
    rw [e2]
    exact Nat.beq_refl _

end CFSG.F3.Planes

end
