module

public import Certificates.Data.Kernel.J4TreeCode
public import CFSG.Certificates.Kernel.Co1BMulSound
public import CFSG.Certificates.Kernel.J4Q.RepQT2B

public section

namespace CFSG.KC.J4Tree

open CFSG.J4Tree.Native CFSG.KC.F2W CFSG.KC.Co1F2 CFSG.KC.J4Q CFSG.Sporadic.J4.Native

@[expose] def RC (a : Code) (P : Nat) : Prop := a.rows = unpackR 12 P

theorem packL_field : ∀ (l : List Nat), (∀ x ∈ l, x < 4096) → ∀ i,
    packL l / 2 ^ (12 * i) % 2 ^ 12 = l.getD i 0
  | [], _, i => by simp [packL]
  | x :: l, h, i => by
    have hx : x < 4096 := h x List.mem_cons_self
    have ih := packL_field l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have e : packL (x :: l) = x + 4096 * packL l := rfl
    rcases i with _ | i
    · rw [e]
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    · rw [e, List.getD_cons_succ, ← ih i, Nat.mul_succ, Nat.add_comm (12 * i) 12, Nat.pow_add,
        ← Nat.div_div_eq_div_mul]
      congr 2
      omega

theorem unpackR_packL {l : List Nat} (hl : l.length = 12) (hb : ∀ x ∈ l, x < 4096) :
    unpackR 12 (packL l) = l.toArray := by
  apply Array.ext
  · simp [unpackR, hl]
  · intro i h1 h2
    simp only [unpackR, Array.getElem_ofFn, List.getElem_toArray]
    rw [packL_field l hb i, List.getD_eq_getElem]

theorem rc_of_wf {a : Code} (h : a.wf = true) : RC a (pkC a) := by
  unfold Code.wf at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  unfold RC pkC
  rw [unpackR_packL (by simpa using h.1) h.2, Array.toArray_toList]

theorem rc_one : RC 1 oneK := rc_of_wf (by decide)

theorem rc_mul {a b : Code} {P Q : Nat} (ha : RC a P) (hb : RC b Q) : RC (a * b) (mulW 12 P Q) := by
  change (Code.mul a b).rows = _
  unfold Code.mul
  change CFSG.Sporadic.SmallF2.Native.mulRows 12 a.rows b.rows = _
  rw [ha, hb, mulRows_unpackW]

theorem rc_eq {a b : Code} {P : Nat} (ha : RC a P) (hb : RC b P) : a = b := by
  cases a
  cases b
  simp only [RC] at ha hb
  rw [ha, hb]

theorem rc_beq {a b : Code} {P Q : Nat} (ha : RC a P) (hb : RC b Q) (h : Nat.beq P Q = true) :
    (a == b) = true := by
  rw [Nat.eq_of_beq_eq_true h] at ha
  rw [rc_eq ha hb]
  exact beq_self_eq_true b

theorem rc_row {a : Code} {P : Nat} (ha : RC a P) {i : Nat} (hi : i < 12) :
    a.rows[i]?.getD 0 = P / 2 ^ (12 * i) % 2 ^ 12 := by
  rw [ha]
  simp [unpackR, hi]

theorem rc_get {L : Array Code} (hL : L.toList.all Code.wf = true) (i : Nat) :
    RC (L[i]?.getD 1) ((tblC L).getD i oneK) := by
  by_cases hi : i < L.size
  · have hw : L[i].wf = true := List.all_eq_true.1 hL _ (List.getElem_mem (by simpa using hi))
    have e1 : L[i]?.getD 1 = L[i] := by simp [hi]
    have e2 : (tblC L).getD i oneK = pkC L[i] := by simp [tblC, hi]
    rw [e1, e2]
    exact rc_of_wf hw
  · have e1 : L[i]?.getD 1 = 1 := by simp [hi]
    have e2 : (tblC L).getD i oneK = oneK :=
      List.getD_eq_default _ _ (by simp only [tblC, List.length_map, Array.length_toList]; omega)
    rw [e1, e2]
    exact rc_one

theorem rc_foldl {α : Type} (f : Code → α → Code) (g : Nat → α → Nat)
    (hfg : ∀ a P x, RC a P → RC (f a x) (g P x)) :
    ∀ (l : List α) (a : Code) (P : Nat), RC a P → RC (l.foldl f a) (l.foldl g P)
  | [], _, _, h => h
  | x :: l, a, P, h => rc_foldl f g hfg l _ _ (hfg a P x h)

theorem rc_letterCode (hx : xCode.toList.all Code.wf = true) (hxi : xiCode.toList.all Code.wf = true)
    (ℓ : Int) : RC (letterCode ℓ) (letK (tblC xCode) (tblC xiCode) ℓ) := by
  unfold letterCode letK
  split
  · exact rc_get hx _
  · exact rc_get hxi _

theorem rc_codeOfWord (hx : xCode.toList.all Code.wf = true)
    (hxi : xiCode.toList.all Code.wf = true) (w : List Int) :
    RC (codeOfWord w) (wordCK (tblC xCode) (tblC xiCode) w) :=
  rc_foldl _ _ (fun _ _ ℓ h => rc_mul h (rc_letterCode hx hxi ℓ)) w 1 oneK rc_one

theorem rc_etaCode (hu : uCode.toList.all Code.wf = true) (c : Nat) :
    RC (etaCode c) (etaCK (tblC uCode) c) := by
  unfold etaCode etaCK
  refine rc_foldl _ _ (fun a P j h => ?_) _ 1 oneK rc_one
  split
  · exact rc_mul h (rc_get hu j)
  · exact h

theorem inE_eq {a : Code} {P : Nat} (ha : RC a P) :
    a.inE = (List.range 11).all fun i => P / 2 ^ (12 * (i + 1)) % 2 ^ 12 == 2 ^ (i + 1) := by
  unfold Code.inE
  apply all_range_congr
  intro i hi
  rw [rc_row ha (by omega)]

private theorem foldl_range_congr {f g : Nat → Nat → Nat} (n : Nat)
    (h : ∀ acc j, j < n → f acc j = g acc j) (a : Nat) :
    (List.range n).foldl f a = (List.range n).foldl g a := by
  apply List.foldl_ext
  intro acc j hj
  exact h acc j (List.mem_range.1 hj)

theorem proj12_eq (v : V2) : proj12 v = projN (v2N v) := by
  unfold proj12 projN
  apply foldl_range_congr
  intro acc j hj
  rw [testBit_v2N v (by omega)]

theorem rho12_rows {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
    (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) (hs : secCb.toList.all V2.wf = true)
    {M : Array V2} {m : Nat} (hM : WfA M ∧ encR M = m) :
    (rho12 M).rows.toList = secCb.toList.map fun c => projN (vecJ rm (v2N c) m) := by
  unfold rho12
  simp only [Array.toList_map]
  apply List.map_congr_left
  intro v hv
  rw [proj12_eq, v2N_frApply hK hM.1 (List.all_eq_true.1 hs v hv), hM.2]

theorem rows_eq_of_toList {a b : Code} (h : a.rows.toList = b.rows.toList) : a = b := by
  cases a
  cases b
  simp only [Code.mk.injEq]
  exact Array.ext' h

theorem row_v2N {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
    (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {M : Array V2} {m : Nat}
    (hM : WfA M ∧ encR M = m) {i : Nat} (hi : i < 112) :
    v2N (M[i]?.getD V2.zero) = rowJ rm m i := by
  obtain ⟨-, hrm⟩ := consts_c hK
  rw [hrm, ← hM.2, rowJ_eq (Array.all_eq_true.mp hM.1.2) hi]

end CFSG.KC.J4Tree

end
