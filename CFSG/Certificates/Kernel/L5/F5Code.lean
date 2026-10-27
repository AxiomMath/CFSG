module

public import Certificates.Data.Kernel.L5.F5Code

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

open Equiv Perm CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem dg_enc9 {a0 a1 a2 a3 a4 a5 a6 a7 a8 : Nat} (h0 : a0 < 8) (h1 : a1 < 8) (h2 : a2 < 8)
    (h3 : a3 < 8) (h4 : a4 < 8) (h5 : a5 < 8) (h6 : a6 < 8) (h7 : a7 < 8) (h8 : a8 < 8) :
    dg (enc9 a0 a1 a2 a3 a4 a5 a6 a7 a8) 0 = a0 ∧ dg (enc9 a0 a1 a2 a3 a4 a5 a6 a7 a8) 1 = a1 ∧
      dg (enc9 a0 a1 a2 a3 a4 a5 a6 a7 a8) 2 = a2 ∧ dg (enc9 a0 a1 a2 a3 a4 a5 a6 a7 a8) 3 = a3 ∧
      dg (enc9 a0 a1 a2 a3 a4 a5 a6 a7 a8) 4 = a4 ∧ dg (enc9 a0 a1 a2 a3 a4 a5 a6 a7 a8) 5 = a5 ∧
      dg (enc9 a0 a1 a2 a3 a4 a5 a6 a7 a8) 6 = a6 ∧ dg (enc9 a0 a1 a2 a3 a4 a5 a6 a7 a8) 7 = a7 ∧
      dg (enc9 a0 a1 a2 a3 a4 a5 a6 a7 a8) 8 = a8 := by
  simp only [dg, enc9, Nat.reducePow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem dg_codeP (p : Amb 5) :
    dg (codeP p) 0 = (p.1 0).val ∧ dg (codeP p) 1 = (p.1 1).val ∧ dg (codeP p) 2 = (p.1 2).val ∧
      dg (codeP p) 3 = (p.1 3).val ∧ dg (codeP p) 4 = (p.1 4).val ∧ dg (codeP p) 5 = (p.2 0).val ∧
      dg (codeP p) 6 = (p.2 1).val ∧ dg (codeP p) 7 = (p.2 2).val ∧
      dg (codeP p) 8 = (p.2 3).val := by
  have h : ∀ i : Fin 5, (p.1 i).val < 8 := fun i => by
    have := (p.1 i).isLt
    omega
  have h' : ∀ i : Fin 4, (p.2 i).val < 8 := fun i => by
    have := (p.2 i).isLt
    omega
  exact dg_enc9 (h 0) (h 1) (h 2) (h 3) (h 4) (h' 0) (h' 1) (h' 2) (h' 3)

theorem dg_codeP_fst (p : Amb 5) (i : Fin 5) : dg (codeP p) i.val = (p.1 i).val := by
  obtain ⟨e0, e1, e2, e3, e4, -, -, -, -⟩ := dg_codeP p
  fin_cases i
  exacts [e0, e1, e2, e3, e4]

theorem dg_codeP_snd (p : Amb 5) (i : Fin 4) : dg (codeP p) (5 + i.val) = (p.2 i).val := by
  obtain ⟨-, -, -, -, -, e5, e6, e7, e8⟩ := dg_codeP p
  fin_cases i
  exacts [e5, e6, e7, e8]

theorem codeP_mul (g h : Amb 5) : codeP (g * h) = mulC (codeP g) (codeP h) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := dg_codeP h
  simp only [mulC, e0, e1, e2, e3, e4, e5, e6, e7, e8, dg_codeP_fst, dg_codeP_snd]
  rfl

theorem zC_codeP (p : Amb 5) : zC (codeP p) = decide (p.1 * z5 = z5 * p.1) := by
  obtain ⟨e0, e1, e2, e3, e4, -, -, -, -⟩ := dg_codeP p
  have hz : ∀ v : Fin 5, zN v.val = (z5 v).val := by decide
  have z0 : z5 0 = 1 := by decide
  have z1 : z5 1 = 0 := by decide
  have z2 : z5 2 = 3 := by decide
  have z3 : z5 3 = 2 := by decide
  have z4 : z5 4 = 4 := by decide
  have key : p.1 * z5 = z5 * p.1 ↔ (p.1 1 = z5 (p.1 0) ∧ p.1 0 = z5 (p.1 1) ∧
      p.1 3 = z5 (p.1 2) ∧ p.1 2 = z5 (p.1 3) ∧ p.1 4 = z5 (p.1 4)) := by
    rw [Perm.ext_iff]
    constructor
    · intro h
      have a0 := h 0
      have a1 := h 1
      have a2 := h 2
      have a3 := h 3
      have a4 := h 4
      simp only [Perm.mul_apply, z0, z1, z2, z3, z4] at a0 a1 a2 a3 a4
      exact ⟨a0, a1, a2, a3, a4⟩
    · rintro ⟨a0, a1, a2, a3, a4⟩ x
      have hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
        revert x
        decide
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · simp only [Perm.mul_apply, z0]
        exact a0
      · simp only [Perm.mul_apply, z1]
        exact a1
      · simp only [Perm.mul_apply, z2]
        exact a2
      · simp only [Perm.mul_apply, z3]
        exact a3
      · simp only [Perm.mul_apply, z4]
        exact a4
  rw [Bool.eq_iff_iff, decide_eq_true_iff, key]
  simp only [zC, Bool.and_eq_true, beq_iff_eq, e0, e1, e2, e3, e4, hz, Fin.val_inj, and_assoc]

theorem T5b_conj {g : Amb 5} (hg : g ∈ F5list) {t : Amb 5} (ht : T5b t = true) :
    T5b (g * t * g⁻¹) = zC (codeP (g * t * g⁻¹)) := by
  rw [zC_codeP]
  have hg' := (List.mem_filter.1 hg).2
  rw [decide_eq_true_iff] at hg'
  obtain ⟨hgx, hgs⟩ := hg'
  unfold T5b at ht
  rw [decide_eq_true_iff] at ht
  obtain ⟨htx, hts, -⟩ := ht
  have hgc : Commute g.2 x4 := hgx
  have hc : Commute (g.2 * t.2 * g.2⁻¹) x4 := (hgc.mul_left htx).mul_left hgc.inv_left
  have hs : sign (g.1 * t.1 * g.1⁻¹) = sign (g.2 * t.2 * g.2⁻¹) := by
    simp only [Perm.sign_mul, Perm.sign_inv, hgs, hts]
  unfold T5b
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, hc.eq, hs, true_and]

variable {n : Nat}

theorem f5PairsF_eq (E : Nat → Idx n) (tC : List Nat) (fC : List (Nat × Nat))
    (ht : allT5L.map (fun t : ↥T5 => codeP t.1) = tC)
    (hf : F5list.map (fun g => (codeP g, codeP g⁻¹)) = fC) :
    f5PairsF (fun t : ↥T5 => E (codeP t.1)) = f5P E tC fC := by
  subst ht hf
  unfold f5PairsF f5P
  rw [List.flatMap_map]
  congr 1
  funext t
  rw [List.filterMap_map]
  apply List.filterMap_congr
  intro g hg
  simp only [Function.comp_apply]
  rw [← codeP_mul, ← codeP_mul, ← T5b_conj hg (mem_T5_iff_b.1 t.2)]
  by_cases h : T5b (g * (t : Amb 5) * g⁻¹) = true
  · simp only [h, dite_true, ite_true]
  · simp only [h, dite_false, ite_false, Bool.false_eq_true]

theorem key_lt (p : Idx n × Idx n) : p.1.v * n + p.2.v < n * n := by
  have h1 := Idx.v_lt p.1
  have h2 := Idx.v_lt p.2
  calc p.1.v * n + p.2.v < p.1.v * n + n := by omega
    _ = (p.1.v + 1) * n := by rw [Nat.succ_mul]
    _ ≤ n * n := Nat.mul_le_mul_right n h1

theorem dedup_go (ps : List (Idx n × Idx n)) (arr : Array Bool) (b : Nat)
    (acc : List (Idx n × Idx n)) (hs : arr.size = n * n)
    (hb : ∀ k, k < n * n → arr.getD k false = b.testBit k) :
    (ps.foldl (fun (st : Array Bool × List (Idx n × Idx n)) p =>
      if st.1.getD (p.1.v * n + p.2.v) false then st
      else (st.1.set! (p.1.v * n + p.2.v) true, p :: st.2)) (arr, acc)).2 =
    (ps.foldl (fun (st : Nat × List (Idx n × Idx n)) p =>
      if st.1.testBit (p.1.v * n + p.2.v) then st
      else (st.1 ||| 2 ^ (p.1.v * n + p.2.v), p :: st.2)) (b, acc)).2 := by
  induction ps generalizing arr b acc with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [hb _ (key_lt p)]
    split
    · exact ih arr b acc hs hb
    · refine ih _ _ _ (by simp [hs]) fun k hk => ?_
      simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds, Nat.testBit_or, Nat.testBit_two_pow]
      have hb' := hb k hk
      rw [Array.getD_eq_getD_getElem?] at hb'
      by_cases e : p.1.v * n + p.2.v = k
      · simp [e, hs, hk]
      · simp [e, hb']

theorem foldl_dedupGo (ps : List (Idx n × Idx n)) (b : Nat) (acc : List (Idx n × Idx n)) :
    (ps.foldl (fun (st : Nat × List (Idx n × Idx n)) p =>
      if st.1.testBit (p.1.v * n + p.2.v) then st
      else (st.1 ||| 2 ^ (p.1.v * n + p.2.v), p :: st.2)) (b, acc)).2 =
    (dedupGo b ps).reverse ++ acc := by
  induction ps generalizing b acc with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons, dedupGo]
    split
    · exact ih b acc
    · rw [ih, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem dedupPairs_eq (ps : List (Idx n × Idx n)) : dedupPairs ps = dedupN ps := by
  rw [dedupN, ← List.append_nil (dedupGo 0 ps).reverse, ← foldl_dedupGo]
  exact dedup_go ps _ 0 [] (by simp) fun k hk => by simp [Array.getD_eq_getD_getElem?, hk]

def MarksEq (vis : Array Bool) (b : Nat) : Prop :=
  vis.size = n ∧ ∀ k, k < n → vis.getD k false = b.testBit k

theorem marksEq_set {vis : Array Bool} {b : Nat} (h : MarksEq (n := n) vis b) (y : Idx n) :
    MarksEq (n := n) (vis.set! y.v true) (b ||| 2 ^ y.v) := by
  refine ⟨by simp [h.1], fun k hk => ?_⟩
  have hb := h.2 k hk
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds, Nat.testBit_or, Nat.testBit_two_pow]
  rw [Array.getD_eq_getD_getElem?] at hb
  by_cases e : y.v = k
  · simp [e, h.1, hk]
  · simp [e, hb]

theorem addNew_eq (ys : List (Idx n)) (vis : Array Bool) (b : Nat) (new : List (Idx n))
    (h : MarksEq (n := n) vis b) :
    (addNew vis new ys).2 = (addNewN b new ys).2 ∧
      MarksEq (n := n) (addNew vis new ys).1 (addNewN b new ys).1 := by
  induction ys generalizing vis b new with
  | nil => exact ⟨rfl, h⟩
  | cons y ys ih =>
    unfold addNew at ih ⊢
    simp only [List.foldl_cons, addNewN]
    rw [h.2 y.v (Idx.v_lt y)]
    split
    · exact ih vis b new h
    · exact ih _ _ (y :: new) (marksEq_set h y)

theorem round_eq (steps : Idx n → List (Idx n)) (xs : List (Idx n)) (vis : Array Bool) (b : Nat)
    (new : List (Idx n)) (h : MarksEq (n := n) vis b) :
    (xs.foldl (fun (st : Array Bool × List (Idx n)) x => addNew st.1 st.2 (steps x))
      (vis, new)).2 = (roundN steps b new xs).2 ∧
    MarksEq (n := n) (xs.foldl (fun (st : Array Bool × List (Idx n)) x =>
      addNew st.1 st.2 (steps x)) (vis, new)).1 (roundN steps b new xs).1 := by
  induction xs generalizing vis b new with
  | nil => exact ⟨rfl, h⟩
  | cons x xs ih =>
    obtain ⟨e2, hi⟩ := addNew_eq (steps x) vis b new h
    simp only [List.foldl_cons, roundN]
    rw [← e2]
    exact ih _ _ _ hi

theorem bfsGo_eq (steps : Idx n → List (Idx n)) (fuel : Nat) (vis : Array Bool) (b : Nat)
    (frontier acc : List (Idx n)) (h : MarksEq (n := n) vis b) :
    bfsGo steps fuel vis frontier acc = bfsGoN steps fuel b frontier acc := by
  induction fuel generalizing vis b frontier acc with
  | zero => rfl
  | succ fuel ih =>
    cases frontier with
    | nil => rfl
    | cons x xs =>
      obtain ⟨e2, hi⟩ := round_eq steps (x :: xs) vis b [] h
      simp only [bfsGo, bfsGoN]
      rw [← e2]
      exact ih _ _ _ _ hi

theorem bfs_fun (steps : Idx n → List (Idx n)) : bfs steps = bfsN steps := by
  funext r
  have h0 : MarksEq (n := n) (Array.replicate n false) 0 :=
    ⟨by simp, fun k hk => by simp [Array.getD_eq_getD_getElem?, hk]⟩
  have h1 := marksEq_set h0 r
  rw [Nat.zero_or] at h1
  exact bfsGo_eq steps n _ _ [r] [r] h1

theorem repsGo_fun (steps : Idx n → List (Idx n)) : repsGo steps = repsGoN steps := by
  funext l
  induction l with
  | nil => rfl
  | cons u us ih =>
    funext cov acc
    simp only [repsGo, repsGoN, bfs_fun, ih]

variable [Group (Idx n)]

theorem fusChk_eq
    (emb : ↥T5 → Idx n) (reps : List (Idx n)) (ciA : Array Nat) (invs : List (Idx n))
    (x : Idx n) :
    fusChk emb reps ciA invs x =
      fusChkL (fuseL (f5PairsF emb) (nbarPairsF emb)) (emb x0T5) reps ciA invs x := by
  unfold fusChk fusChkL fuseL fuseF
  simp only [dedupPairs_eq, bfs_fun, repsGo_fun]

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end
