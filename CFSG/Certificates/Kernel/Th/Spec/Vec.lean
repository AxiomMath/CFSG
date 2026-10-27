
module

public import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Certificates.Kernel.Th.Spec.Seed

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier

section Consts

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (K : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)

include K in
theorem frApply_frTable_v4OfNat {X : Array V4} (hX : WfRows X) {M : ℕ}
    (hM : rowsMatrix X = pkMat M) (v : ℕ) :
    frApply (frTable X) (v4OfNat v) = v4OfNat (vecB rm v M) := by
  apply V4.eq_of_toVec_eq (frApply_frTable_wf hX.2 _) (v4OfNat_wf (vecB_lt K v M))
  rw [frApply_frTable_toVec]
  funext i
  simp only [toVec_v4OfNat]
  have h := congrFun (pkVec_vecB K v M) i
  simp only [Matrix.vecMul, dotProduct] at h
  change _ = pkVec (vecB rm v M) i
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← rowsMatrix_apply, hM]
  rfl

end Consts

@[expose] def keyNat (k : Key) : ℕ := k.u.toNat + 2 ^ 256 * k.v.toNat

theorem keyNat_injective : Function.Injective keyNat := by
  intro k k' h
  have hu := V4.toNat_lt k.u
  have hu' := V4.toNat_lt k'.u
  unfold keyNat at h
  have e1 : k.u.toNat = k'.u.toNat := by omega
  have e2 : k.v.toNat = k'.v.toNat := by omega
  cases k
  cases k'
  exact congrArg₂ Key.mk (V4.toNat_inj.1 e1) (V4.toNat_inj.1 e2)

theorem toNat_xor (a b : V4) : (a.xor b).toNat = a.toNat ^^^ b.toNat := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 256
  · rw [Nat.testBit_xor, V4.testBit_toNat _ hj, V4.testBit_toNat _ hj, V4.testBit_toNat _ hj,
      V4.testBit_xor]
  · have h256 : 2 ^ 256 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow ((V4.toNat_lt _).trans_le h256),
      Nat.testBit_lt_two_pow ((Nat.xor_lt_two_pow (V4.toNat_lt a) (V4.toNat_lt b)).trans_le h256)]

theorem cmin_eq (a b : ℕ) : cmin a b = if a < b then a else b := by
  unfold cmin
  by_cases h : a < b
  · have : Nat.blt a b = true := by simpa [Nat.blt_eq] using h
    rw [this, if_pos h]
  · have : Nat.blt a b = false := Bool.eq_false_iff.2 (by simpa [Nat.blt_eq] using h)
    rw [this, if_neg h]

theorem cmax_eq (a b : ℕ) : cmax a b = if a < b then b else a := by
  unfold cmax
  by_cases h : a < b
  · have : Nat.blt a b = true := by simpa [Nat.blt_eq] using h
    rw [this, if_pos h]
  · have : Nat.blt a b = false := Bool.eq_false_iff.2 (by simpa [Nat.blt_eq] using h)
    rw [this, if_neg h]

theorem canon2_eq {u v : ℕ} (hu : u < 2 ^ 256) (hv : v < 2 ^ 256) :
    canon2 u v = cmin u (cmin v (u ^^^ v)) + 2 ^ 256 *
      cmax (cmin u v) (cmin (cmax u v) (u ^^^ v)) := by
  have hs : u ^^^ v < 2 ^ 256 := Nat.xor_lt_two_pow hu hv
  have hlo : cmin u (cmin v (u ^^^ v)) < 2 ^ 256 := by
    simp only [cmin_eq]; split_ifs <;> omega
  unfold canon2 canon3
  change cmin u (cmin v (u ^^^ v)) ||| (cmax (cmin u v) (cmin (cmax u v) (u ^^^ v)) <<< 256) = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlo, Nat.shiftLeft_eq]
  omega

theorem keyNat_canon (p q : V4) : keyNat (canon p q) = canon2 p.toNat q.toNat := by
  have hp := V4.toNat_lt p
  have hq := V4.toNat_lt q
  have hs : (p.xor q).toNat = p.toNat ^^^ q.toNat := toNat_xor p q
  have hs' := V4.toNat_lt (p.xor q)
  rw [canon2_eq hp hq, ← hs]
  unfold canon keyNat
  simp only [V4.lt_iff, cmin_eq, cmax_eq]
  split_ifs <;> simp_all <;> omega

theorem v4OfNat_toNat_self (a : V4) : v4OfNat a.toNat = a :=
  V4.toNat_inj.1 (by rw [v4OfNat_toNat, Nat.mod_eq_of_lt (V4.toNat_lt a)])

section Consts2

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (K : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)

include K in
theorem imageKey_eq_self {X : Array V4} (hX : WfRows X) {M : ℕ} (hM : rowsMatrix X = pkMat M)
    (k : Key)
    (h : canon2 (vecB rm (Nat.land (keyNat k) (2 ^ 256 - 1)) M)
      (vecB rm (Nat.shiftRight (keyNat k) 256) M) = keyNat k) :
    imageKey (frTable X) k = k := by
  have hu : Nat.land (keyNat k) (2 ^ 256 - 1) = k.u.toNat := by
    have h256 := V4.toNat_lt k.u
    change keyNat k &&& (2 ^ 256 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    unfold keyNat
    omega
  have hv : Nat.shiftRight (keyNat k) 256 = k.v.toNat := by
    have h256 := V4.toNat_lt k.u
    change keyNat k >>> 256 = _
    rw [Nat.shiftRight_eq_div_pow]
    unfold keyNat
    omega
  rw [hu, hv] at h
  apply keyNat_injective
  have e1 := frApply_frTable_v4OfNat K hX hM k.u.toNat
  have e2 := frApply_frTable_v4OfNat K hX hM k.v.toNat
  rw [v4OfNat_toNat_self] at e1 e2
  unfold imageKey
  rw [e1, e2, keyNat_canon, v4OfNat_toNat_of_lt (vecB_lt K _ M),
    v4OfNat_toNat_of_lt (vecB_lt K _ M)]
  exact h

end Consts2

end CFSG.KC.Th.Spec

end
