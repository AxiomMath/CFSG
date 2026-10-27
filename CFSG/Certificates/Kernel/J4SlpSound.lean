module

public import Certificates.Data.Kernel.J4Slp
public import CFSG.Certificates.Kernel.SporSch.J4SPairSound
public import CFSG.Sporadic.Schreier.J4SElevenData

public section

namespace CFSG.KC.J4Slp

open CFSG.KC.J4Q CFSG.KC.Loop CFSG.KS.SporSch.J4B CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ
open CFSG.Sporadic.SmallF2.Native

@[expose] def RegsOK (n : Nat) (R : Array Pair) (K : List Nat) : Prop :=
  R.size = n ∧ K.length = 2 * n ∧ ∀ r < n, PairOK R[r]! (regM K r) (regI K r)

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem andB_parts {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem strictL_eq (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by
  cases y <;> rfl

private theorem forceL_eq : ∀ (l : List Nat) (k : List Nat → List Nat), forceL l k = k l
  | [], _ => rfl
  | x :: l, k => by
    show strictL x (fun a => forceL l fun t => k (a :: t)) = _
    rw [strictL_eq]
    exact forceL_eq l fun t => k (x :: t)

private theorem slp_length_setN : ∀ (l : List Nat) (k v : Nat), (J4Slp.setN l k v).length = l.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | x :: l, k + 1, v => by
    change (x :: J4Slp.setN l k v).length = _
    rw [List.length_cons, slp_length_setN l k v, List.length_cons]

private theorem slp_getN_setN (d : Nat) : ∀ (l : List Nat) (k v r : Nat), k < l.length →
    getN d (J4Slp.setN l k v) r = if r = k then v else getN d l r
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, 0, _ => rfl
  | _ :: _, 0, _, _ + 1, _ => rfl
  | _ :: l, k + 1, v, 0, _ => rfl
  | x :: l, k + 1, v, r + 1, h => by
    change getN d (J4Slp.setN l k v) r = _
    rw [slp_getN_setN d l k v r (by simp at h; omega)]
    simp only [Nat.add_right_cancel_iff]
    rfl

private theorem slp_length_setR (K : List Nat) (k x y : Nat) : (setR K k x y).length = K.length := by
  show (J4Slp.setN (J4Slp.setN K (2 * k) x) (2 * k + 1) y).length = K.length
  rw [slp_length_setN, slp_length_setN]

private theorem regM_setR {K : List Nat} {k x y : Nat} (hk : 2 * k + 1 < K.length) (r : Nat) :
    regM (setR K k x y) r = if r = k then x else regM K r := by
  show getN 0 (J4Slp.setN (J4Slp.setN K (2 * k) x) (2 * k + 1) y) (2 * r) =
    if r = k then x else getN 0 K (2 * r)
  have hl : 2 * k + 1 < (J4Slp.setN K (2 * k) x).length := by rw [slp_length_setN]; exact hk
  have hl' : 2 * k < K.length := by omega
  rw [slp_getN_setN 0 _ _ _ _ hl, if_neg (show ¬ (2 * r = 2 * k + 1) by omega),
    slp_getN_setN 0 _ _ _ _ hl']
  by_cases h : r = k
  · rw [if_pos (show 2 * r = 2 * k by omega), if_pos h]
  · rw [if_neg (show ¬ (2 * r = 2 * k) by omega), if_neg h]

private theorem regI_setR {K : List Nat} {k x y : Nat} (hk : 2 * k + 1 < K.length) (r : Nat) :
    regI (setR K k x y) r = if r = k then y else regI K r := by
  show getN 0 (J4Slp.setN (J4Slp.setN K (2 * k) x) (2 * k + 1) y) (2 * r + 1) =
    if r = k then y else getN 0 K (2 * r + 1)
  have hl : 2 * k + 1 < (J4Slp.setN K (2 * k) x).length := by rw [slp_length_setN]; exact hk
  have hl' : 2 * k < K.length := by omega
  rw [slp_getN_setN 0 _ _ _ _ hl]
  by_cases h : r = k
  · rw [if_pos (show 2 * r + 1 = 2 * k + 1 by omega), if_pos h]
  · rw [if_neg (show ¬ (2 * r + 1 = 2 * k + 1) by omega), if_neg h, slp_getN_setN 0 _ _ _ _ hl',
      if_neg (show ¬ (2 * r + 1 = 2 * k) by omega)]

private theorem regsOK_set {n : Nat} {R : Array Pair} {K : List Nat} (hR : RegsOK n R K) {k : Nat}
    (hk : k < n) {P : Pair} {x y : Nat} (hP : PairOK P x y) :
    RegsOK n (R.setIfInBounds k P) (setR K k x y) := by
  obtain ⟨hs, hl, hr⟩ := hR
  have hk' : 2 * k + 1 < K.length := by omega
  refine ⟨by rw [Array.size_setIfInBounds, hs], by rw [slp_length_setR, hl], fun r hrn => ?_⟩
  have hrs : r < R.size := by omega
  have hrs' : r < (R.setIfInBounds k P).size := by rw [Array.size_setIfInBounds]; exact hrs
  rw [getElem!_pos (R.setIfInBounds k P) r hrs', Array.getElem_setIfInBounds hrs, regM_setR hk',
    regI_setR hk']
  by_cases h : r = k
  · subst h
    rw [if_pos rfl, if_pos rfl, if_pos rfl]
    exact hP
  · rw [if_neg (Ne.symm h), if_neg h, if_neg h, ← getElem!_pos R r hrs]
    exact hr r hrn

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
variable (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
include hK

private theorem step_ok {n : Nat} {R : Array Pair} {K : List Nat} (hR : RegsOK n R K) (ins : Instr)
    (hlt : ins.lt n = true) : RegsOK n (Instr.runN O R ins) (stepK c rm one K (instrCode ins)) := by
  have hP : ∀ r < n, PairOK R[r]! (regM K r) (regI K r) := hR.2.2
  cases ins with
  | mu i j k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
    obtain ⟨⟨hi, hj⟩, hk⟩ := hlt
    have e : stepK c rm one K (instrCode (.mu i j k)) =
        setR K k (mulJ c rm (regM K i) (regM K j)) (mulJ c rm (regI K j) (regI K i)) := rfl
    have e' : Instr.runN O R (.mu i j k) = R.setIfInBounds k (mulP R[i]! R[j]!) := rfl
    rw [e, e']
    exact regsOK_set hR hk (mulP_ok hK (hP i hi) (hP j hj))
  | iv i k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
    obtain ⟨hi, hk⟩ := hlt
    have e : stepK c rm one K (instrCode (.iv i k)) = setR K k (regI K i) (regM K i) := rfl
    have e' : Instr.runN O R (.iv i k) = R.setIfInBounds k (invP R[i]!) := rfl
    rw [e, e']
    exact regsOK_set hR hk (invP_ok (hP i hi))
  | pwr e i k =>
    simp only [Instr.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
    obtain ⟨hi, hk⟩ := hlt
    have e1 : stepK c rm one K (instrCode (.pwr e i k)) =
        setR K k (powJ c rm one (regM K i) e) (powJ c rm one (regI K i) e) := rfl
    have e' : Instr.runN O R (.pwr e i k) = R.setIfInBounds k (powP R[i]! e) := rfl
    rw [e1, e']
    exact regsOK_set hR hk (powP_ok hK (hP i hi) e)

theorem runK_ok {n : Nat} {R : Array Pair} {K : List Nat} (hR : RegsOK n R K) (prog : List Instr)
    (hlt : prog.all (Instr.lt n) = true) :
    RegsOK n (runProgN O R prog) (runK c rm one (prog.map instrCode) K) := by
  induction prog generalizing R K with
  | nil => exact hR
  | cons ins prog ih =>
    rw [List.all_cons, Bool.and_eq_true] at hlt
    have e1 : runProgN O R (ins :: prog) = runProgN O (Instr.runN O R ins) prog := rfl
    have e2 : runK c rm one ((ins :: prog).map instrCode) K =
        runK c rm one (prog.map instrCode) (stepK c rm one K (instrCode ins)) := by
      show forceL (stepK c rm one K (instrCode ins)) (runK c rm one (prog.map instrCode)) = _
      exact forceL_eq _ _
    rw [e1, e2]
    exact ih (step_ok hK hR ins hlt.1) hlt.2

theorem vec_pair {P : Pair} {a b : Nat} (hP : PairOK P a b) (v : Nat) :
    O.vmul v P.1 = vecJ rm v a := by
  rw [← hP.1.2]
  exact vec_enc hK hP.1.1 v

theorem chk11_sound {K : List Nat} {p : Nat} (h1 : PairOK H1n (regM K 1) (regI K 1))
    (h2 : PairOK H2n (regM K 2) (regI K 2)) (h : chk11 c rm one p K = true) :
    O.vmul p QXn.1 = p ∧ O.vmul p QZn.1 % 2 ^ 112 ≠ p := by
  have pS : PairOK S5n _ _ := powP_ok hK h2 8
  have pX0 : PairOK X0n _ _ :=
    mulP_ok hK (mulP_ok hK (mulP_ok hK pS (invP_ok h1)) (invP_ok pS)) h1
  have pU := mulP_ok hK h1 h2
  have pY0 : PairOK Y0n _ _ :=
    mulP_ok hK (mulP_ok hK (mulP_ok hK pS pU) (invP_ok pS)) (invP_ok pU)
  have pQX : PairOK QXn _ _ := mulP_ok hK pX0 (powP_ok hK pY0 7)
  have pQY : PairOK QYn _ _ := powP_ok hK pY0 3
  unfold chk11 at h
  simp only [strictB_eq] at h
  obtain ⟨hx, hz⟩ := andB_parts h
  have hx' : O.vmul p QXn.1 = p := by
    rw [vec_pair hK pQX]
    exact Nat.eq_of_beq_eq_true hx
  refine ⟨hx', fun e => ?_⟩
  have hQZ : QZn.1 = O.mul (O.mul (O.mul QXn.1 QYn.1) QXn.2) QYn.2 := rfl
  have w1 := (mul_enc hK pQX.1.1 pQY.1.1).1
  have w2 := (mul_enc hK w1 pQX.2.1).1
  have ev : O.vmul p QZn.1 = vecJ rm (vecJ rm (vecJ rm (vecJ rm p (encN QXn.1)) (encN QYn.1))
      (encN QXn.2)) (encN QYn.2) := by
    change vecMulN 112 QZn.1 p = _
    rw [hQZ, vec_mul w2 pQY.2.1, vec_mul w1 pQX.2.1, vec_mul pQX.1.1 pQY.1.1,
      vec_enc hK pQX.1.1, vec_enc hK pQY.1.1, vec_enc hK pQX.2.1, vec_enc hK pQY.2.1]
  rw [ev, pQX.1.2, pQY.1.2, pQX.2.2, pQY.2.2] at e
  rw [show Nat.mod _ (Nat.pow 2 112) = _ from e, Nat.beq_refl] at hz
  exact absurd hz (by decide)

end CFSG.KC.J4Slp

end
