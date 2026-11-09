module

public import Certificates.Data.Kernel.OpsLayTab
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.OpsLayMcertSound
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace CFSG.KC.OpsLayTab

open CFSG.SectionRank.Native CFSG.KC.OpsK CFSG.KC.OpsMN

variable {V : Type} (O : Ops Nat V)

theorem testBit_pset (P t v j : Nat) (hv : v < 2 ^ 16) :
    (pset P t v).testBit j =
      if 16 * t ≤ j ∧ j < 16 * t + 16 then v.testBit (j - 16 * t) else P.testBit j := by
  have h1 : Nat.shiftLeft 1 (Nat.mul 16 t) = 2 ^ (16 * t) := by
    change 1 <<< (16 * t) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  unfold pset
  rw [h1]
  change ((((P >>> (16 * (t + 1))) <<< (16 * (t + 1))) ||| (v <<< (16 * t))) |||
    P % 2 ^ (16 * t)).testBit j = _
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_mod_two_pow]
  by_cases ha : j < 16 * t
  · have h2 : ¬ j ≥ 16 * (t + 1) := by omega
    have h3 : ¬ j ≥ 16 * t := by omega
    simp [ha, h2, h3]
  · by_cases hb : j < 16 * t + 16
    · have h2 : ¬ j ≥ 16 * (t + 1) := by omega
      have h3 : j ≥ 16 * t := by omega
      have h4 : 16 * t ≤ j ∧ j < 16 * t + 16 := by omega
      simp [ha, h2, h3, h4]
    · have hc : j ≥ 16 * (t + 1) := by omega
      have hv' : v.testBit (j - 16 * t) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))
      have he : 16 * (t + 1) + (j - 16 * (t + 1)) = j := by omega
      have h4 : ¬ (16 * t ≤ j ∧ j < 16 * t + 16) := by omega
      simp [ha, hc, hv', he, h4]

theorem pget_pset (P t v r : Nat) (hv : v < 65536) :
    pget (pset P t v) r = if r = t then v else pget P r := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hm : (65536 : Nat) = 2 ^ 16 := rfl
  rw [hm] at hv
  have hg : ∀ Q, pget Q r = (Q >>> (16 * r)) % 2 ^ 16 := fun _ => rfl
  rw [hg, hg]
  by_cases hr : r = t
  · subst r
    simp only [↓reduceIte, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      testBit_pset P _ v _ hv]
    by_cases hi : i < 16
    · have : 16 * t ≤ 16 * t + i ∧ 16 * t + i < 16 * t + 16 := by omega
      simp [hi, this]
    · simp only [hi, decide_false, Bool.false_and]
      exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv
        (Nat.pow_le_pow_right (by omega) (by omega)))).symm
  · simp only [hr, ↓reduceIte, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      testBit_pset P t v _ hv]
    by_cases hi : i < 16
    · have : ¬ (16 * t ≤ 16 * r + i ∧ 16 * r + i < 16 * t + 16) := by omega
      simp [hi, this]
    · simp [hi]

theorem getN_regsT {T : BTr (BTr Nat)} {n P i : Nat} (hi : i < n) :
    getN (regsT T n P) i = tget 0 T (pget P i) := by
  simp [getN, regsT, List.getD_eq_getElem?_getD, hi]

theorem set_regsT {T : BTr (BTr Nat)} {n P t v : Nat} (ht : t < n) (hv : v < 65536) :
    (regsT T n P).set t (tget 0 T v) = regsT T n (pset P t v) := by
  apply List.ext_getElem (by simp [regsT])
  intro r h1 h2
  simp only [regsT, List.getElem_set, List.getElem_map, List.getElem_range, pget_pset P t v r hv]
  by_cases h : r = t
  · subst h
    simp
  · simp [h, Ne.symm h]

section Gen

variable {mu pw : Nat → Nat → Nat} {st : List Nat → Op → List Nat}
  (hmul : ∀ R i j t, i < R.length → j < R.length →
    st R (.mul i j t) = R.set t (mu (getN R i) (getN R j)))
  (hpow : ∀ R e i t, i < R.length → st R (.pow e i t) = R.set t (pw (getN R i) e))
include hmul hpow

theorem stepF_regsT {T : BTr (BTr Nat)} {K N n : Nat}
    (hT : ∀ v, 2 < v → v < N → entF mu pw T (keyAt K v) v = true) {P v : Nat} {op : Op}
    (h : opT K N n P v op = true) :
    st (regsT T n P) op = regsT T n (pset P (tgtOf op) v) := by
  have hl : (regsT T n P).length = n := by simp [regsT]
  cases op with
  | mul i j t =>
    simp only [opT, keyEq, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨⟨h2, hN⟩, h16⟩, ⟨⟨hi, hj⟩, ht⟩, ⟨h1, hb⟩, hc⟩ := h
    have he := hT v h2 hN
    unfold entF at he
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true hb, Nat.eq_of_beq_eq_true hc,
      Nat.rec_zero] at he
    change st (regsT T n P) (.mul i j t) = regsT T n (pset P t v)
    rw [hmul _ _ _ _ (by omega) (by omega), getN_regsT hi, getN_regsT hj,
      ← Nat.eq_of_beq_eq_true he, set_regsT ht h16]
  | pow e i t =>
    simp only [opT, keyEq, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨⟨h2, hN⟩, h16⟩, ⟨hi, ht⟩, ⟨h1, hb⟩, _⟩ := h
    have he := hT v h2 hN
    unfold entF at he
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true hb] at he
    have he' : Nat.beq (tget 0 T v) (pw (tget 0 T (pget P i)) e) = true := he
    change st (regsT T n P) (.pow e i t) = regsT T n (pset P t v)
    rw [hpow _ _ _ _ (by omega), getN_regsT hi, ← Nat.eq_of_beq_eq_true he', set_regsT ht h16]

theorem fold_symF {T : BTr (BTr Nat)} {K N n : Nat}
    (hT : ∀ v, 2 < v → v < N → entF mu pw T (keyAt K v) v = true) :
    ∀ (ops : List Op) (vs : List Nat) (P P' : Nat), symT K N n ops vs P P' = true →
      ops.foldl st (regsT T n P) = regsT T n P'
  | [], [], P, P', h => by
    have h' : Nat.beq P P' = true := h
    rw [Nat.eq_of_beq_eq_true h']
    rfl
  | [], _ :: _, _, _, h => by simp [symT] at h
  | _ :: _, [], _, _, h => by simp [symT] at h
  | op :: ops, v :: vs, P, P', h => by
    change (opT K N n P v op &&
      forceB (pset P (tgtOf op) v) fun Q => symT K N n ops vs Q P') = true at h
    rw [Bool.and_eq_true, forceB_eq] at h
    rw [List.foldl_cons, stepF_regsT hmul hpow hT h.1]
    exact fold_symF hT ops vs _ P' h.2

end Gen

theorem tab_of_chunksF {mu pw : Nat → Nat → Nat} {T : BTr (BTr Nat)} {K : Nat} {N k m : Nat}
    (hm : N ≤ 3 + m * k) (h : ∀ i < m, tabF mu pw T K N (3 + i * k) k = true) :
    ∀ v, 2 < v → v < N → entF mu pw T (keyAt K v) v = true := by
  intro v h2 hN
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 => by subst h0; omega
  have hd := Nat.div_add_mod' (v - 3) k
  have hr := Nat.mod_lt (v - 3) hk
  have hq : (v - 3) / k < m := (Nat.div_lt_iff_lt_mul hk).2 (by omega)
  have hc := h _ hq
  unfold tabF at hc
  rw [List.all_eq_true] at hc
  have hx := hc v (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  have hb : Nat.blt v N = true := by simpa [Nat.blt_eq] using hN
  rw [hb, Bool.not_true, Bool.false_or] at hx
  exact hx

theorem fold_symT {T : BTr (BTr Nat)} {K N n : Nat}
    (hT : ∀ v, 2 < v → v < N → entT O T (keyAt K v) v = true)
    (ops : List Op) (vs : List Nat) (P P' : Nat) (h : symT K N n ops vs P P' = true) :
    ops.foldl (stepL O) (regsT T n P) = regsT T n P' :=
  fold_symF (mu := O.mul) (pw := fun x e => powN O (e + 1) x e) (fun _ _ _ _ _ _ => rfl)
    (fun R e i t _ => by
      change R.set t (O.pow (getN R i) e) = _
      rw [← powN_eq O _ _ _ (Nat.lt_succ_self e)])
    hT ops vs P P' h

open CFSG.KC.OpsLayK (getR stepV powK) in
open CFSG.KC.OpsLayK.Snd (runL) in
theorem runL_of_symF {c : CFSG.KC.LQT.Lay} {T : BTr (BTr Nat)} {K N n : Nat}
    (hT : ∀ v, 2 < v → v < N → entF c.mul (powK c) T (keyAt K v) v = true)
    (ops : List Op) (vs : List Nat) (P P' : Nat) (h : symT K N n ops vs P P' = true) :
    runL c ops (regsT T n P) = regsT T n P' := by
  have hg : ∀ (R : List Nat) i, i < R.length → getR c R i = getN R i := fun R i hi => by
    simp only [getR, getN, List.getD_eq_getElem _ _ hi]
  exact fold_symF (st := fun R o => R.set (CFSG.KC.OpsLayK.Op.tgt o) (stepV c R o))
    (fun R i j t hi hj => by
      change R.set t (c.mul (getR c R i) (getR c R j)) = _
      rw [hg R i hi, hg R j hj])
    (fun R e i t hi => by
      change R.set t (powK c (getR c R i) e) = _
      rw [hg R i hi])
    hT ops vs P P' h

theorem tab_of_chunks {T : BTr (BTr Nat)} {K : Nat} {N k m : Nat}
    (hm : N ≤ 3 + m * k) (h : ∀ i < m, tabT O T K N (3 + i * k) k = true) :
    ∀ v, 2 < v → v < N → entT O T (keyAt K v) v = true :=
  tab_of_chunksF (mu := O.mul) (pw := fun x e => powN O (e + 1) x e) hm h

end CFSG.KC.OpsLayTab

end
