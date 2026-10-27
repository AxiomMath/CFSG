module

public import CFSG.Certificates.Kernel.Spor.PK.F42MatMul
public import CFSG.Certificates.Kernel.Spor.PK.F42Parse

public section

namespace CFSG.KS.PK

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.F42 CFSG.F3.Native
open CFSG.LieType.Multipliers.F42 (Pair refVal slpStep pairUp parseInts)

private theorem imp_bool_iff (a b : Bool) : (!a || b) = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp

theorem refK_eq (F I : List ℕ) (c : ℕ) :
    refK F I c = if c % 2 = 0 then F.getD (c / 2) 0 else I.getD (c / 2) 0 := by
  unfold refK
  rw [nthV_eq, nthV_eq]
  by_cases h : c % 2 = 0
  · have hb : Nat.beq (Nat.mod c 2) 0 = true := by rw [Nat.beq_eq]; exact h
    rw [if_pos h]
    show Bool.rec (motive := fun _ => Nat) _ _ (Nat.beq (Nat.mod c 2) 0) = _
    rw [hb]
    rfl
  · have hb : Nat.beq (Nat.mod c 2) 0 = false := by
      cases hh : Nat.beq (Nat.mod c 2) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hh) h
    rw [if_neg h]
    show Bool.rec (motive := fun _ => Nat) _ _ (Nat.beq (Nat.mod c 2) 0) = _
    rw [hb]
    rfl

theorem refOK_iff (F I : List ℕ) (n c : ℕ) :
    refOK F I n c = true ↔ c / 2 < n ∧
      (c % 2 = 1 → mulS (F.getD (c / 2) 0) (I.getD (c / 2) 0) = idS) := by
  have h1 : Nat.blt (Nat.div c 2) n = true ↔ c / 2 < n := by rw [Nat.blt_eq]; rfl
  have h2 : Nat.beq (Nat.mod c 2) 1 = true ↔ c % 2 = 1 := by rw [Nat.beq_eq]; rfl
  have h3 : Nat.beq (mulS (nthV F (Nat.div c 2)) (nthV I (Nat.div c 2))) idS = true ↔
      mulS (F.getD (c / 2) 0) (I.getD (c / 2) 0) = idS := by
    rw [Nat.beq_eq, nthV_eq, nthV_eq]; rfl
  unfold refOK
  rw [andB_eq, impB_eq, Bool.and_eq_true, imp_bool_iff, h1, h2, h3]

theorem insK_iff (F I R : List ℕ) (t : ℕ) :
    insK F I R t = true ↔ refOK F I (t + 2) (R.getD (2 * t) 0) = true ∧
      refOK F I (t + 2) (R.getD (2 * t + 1) 0) = true ∧
      mulS (refK F I (R.getD (2 * t) 0)) (refK F I (R.getD (2 * t + 1) 0)) = F.getD (t + 2) 0 := by
  unfold insK
  simp only [letB_eq, andB_eq, Bool.and_eq_true, nthV_eq, Nat.beq_eq]
  exact Iff.rfl

theorem insChunk_iff (F I R : List ℕ) (m lo n : ℕ) :
    insChunk F I R m lo n = true ↔ ∀ d < n, lo + d < m → insK F I R (lo + d) = true := by
  unfold insChunk
  simp only [allN_lqt_iff, impB_eq, imp_bool_iff, Nat.blt_eq]
  exact Iff.rfl

theorem ins_all {F I Rc : List ℕ} {nI nP : ℕ}
    (hins : ∀ c < nP, insChunk F I Rc nI (16 * c) 16 = true) (hnP : nI ≤ 16 * nP) :
    ∀ t < nI, insK F I Rc t = true := by
  intro t ht
  have h1 : t / 16 < nP := by omega
  have h2 := (insChunk_iff F I Rc nI (16 * (t / 16)) 16).1 (hins (t / 16) h1) (t % 16) (by omega)
    (by omega)
  have h3 : 16 * (t / 16) + t % 16 = t := by omega
  rwa [h3] at h2

theorem startK_iff {cA cB F I : List ℕ} :
    startK cA cB F I = true ↔ F.getD 0 0 = decodeK cA ∧ F.getD 1 0 = decodeK cB ∧
      mulS (decodeK cA) (decodeK cA) = idS ∧
      mulS (decodeK cB) (mulS (decodeK cB) (decodeK cB)) = idS ∧
      mulS (decodeK cA) (I.getD 0 0) = idS ∧ mulS (decodeK cB) (I.getD 1 0) = idS := by
  unfold startK
  simp only [letB_eq, andB_eq, Bool.and_eq_true, nthV_eq, Nat.beq_eq]

theorem liftsK_iff {F I LR LF LI : List ℕ} {n : ℕ} :
    liftsK F I LR LF LI n = true ↔ LR.length = 48 ∧ ∀ k < 48,
      refOK F I n (LR.getD k 0) = true ∧ refOK F I n (Nat.xor (LR.getD k 0) 1) = true ∧
      LF.getD k 0 = refK F I (LR.getD k 0) ∧ LI.getD k 0 = refK F I (Nat.xor (LR.getD k 0) 1) := by
  unfold liftsK
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, lenN_misc_eq, allN_lqt_iff, letB_eq, nthV_eq]

@[expose] def f42Init (pA pB : String) : Array Pair :=
  #[(rowsOf 52 pA, rowsOf 52 pA), (rowsOf 52 pB, mul 52 (rowsOf 52 pB) (rowsOf 52 pB))]

@[expose] def f42Nodes (init : Array Pair) (Rc : List ℕ) (t : ℕ) : Array Pair :=
  ((List.range t).map fun s => (refOfCode (Rc.getD (2 * s) 0), refOfCode (Rc.getD (2 * s + 1) 0))).foldl
    slpStep init

theorem f42Nodes_zero (init : Array Pair) (Rc : List ℕ) : f42Nodes init Rc 0 = init := rfl

theorem f42Nodes_succ (init : Array Pair) (Rc : List ℕ) (t : ℕ) :
    f42Nodes init Rc (t + 1) =
      slpStep (f42Nodes init Rc t) (refOfCode (Rc.getD (2 * t) 0), refOfCode (Rc.getD (2 * t + 1) 0)) := by
  unfold f42Nodes
  rw [List.range_succ, List.map_append, List.foldl_append]
  rfl

private theorem pairUp_map_refOfCode_aux : ∀ Rc : List ℕ,
    pairUp (Rc.map refOfCode) = (List.range (Rc.length / 2)).map fun s =>
      (refOfCode (Rc.getD (2 * s) 0), refOfCode (Rc.getD (2 * s + 1) 0))
  | [] => rfl
  | [a] => by simp [pairUp]
  | a :: b :: l => by
    have ih := pairUp_map_refOfCode_aux l
    have hl : (a :: b :: l).length / 2 = l.length / 2 + 1 := by
      simp only [List.length_cons]; omega
    rw [List.map_cons, List.map_cons, pairUp, ih, hl, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    refine congrArg₂ List.cons rfl (List.map_congr_left fun s _ => ?_)
    simp only [Function.comp, List.getD_cons_succ, Nat.mul_succ]

theorem pairUp_map_refOfCode (Rc : List ℕ) :
    pairUp (Rc.map refOfCode) = (List.range (Rc.length / 2)).map fun s =>
      (refOfCode (Rc.getD (2 * s) 0), refOfCode (Rc.getD (2 * s + 1) 0)) := by
  exact pairUp_map_refOfCode_aux Rc

theorem slpValsOf_eq {pA pB slp : String} {cS Rc : List ℕ} (hS : slp = strOf cS)
    (hfmt : fmtK cS = true) (hints : eqLN (intsK cS) Rc = true) :
    slpValsOf pA pB slp = f42Nodes (f42Init pA pB) Rc (Rc.length / 2) := by
  have h1 : parseInts slp = (intsK cS).map refOfCode := by
    rw [hS]; exact parseInts_strL_eq_intsK hfmt
  have h2 : intsK cS = Rc := by simpa [eqLN_eq] using hints
  unfold slpValsOf f42Nodes f42Init
  rw [h1, h2, pairUp_map_refOfCode]

theorem refVal_refOfCode (vals : Array Pair) (c : ℕ) :
    refVal vals (refOfCode c) = if c % 2 = 0 then vals[c / 2]! else (vals[c / 2]!).swap := by
  unfold refVal refOfCode
  by_cases h : c % 2 = 0
  · rw [if_pos h, if_pos h, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]
  · have e : (-(-((c / 2 : ℕ) : ℤ) - 1) - 1) = ((c / 2 : ℕ) : ℤ) := by omega
    rw [if_neg h, if_neg h, if_neg (by omega), e, Int.toNat_natCast]

private theorem push_getElem!_lt {α : Type _} [Inhabited α] (xs : Array α) (x : α) {k : ℕ}
    (hk : k < xs.size) : (xs.push x)[k]! = xs[k]! := by
  rw [getElem!_pos (xs.push x) k (by rw [Array.size_push]; omega), getElem!_pos xs k hk,
    Array.getElem_push_lt hk]

private theorem push_getElem!_eq {α : Type _} [Inhabited α] (xs : Array α) (x : α) :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos (xs.push x) xs.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]

private theorem strOf_eq_strL (l : List ℕ) : strOf l = strL l := rfl


structure F42NodeRel (F I : List ℕ) (vals : Array Pair) (n : ℕ) : Prop where
  size_eq : vals.size = n
  can_fst : ∀ k < n, Can52 vals[k]!.1
  can_snd : ∀ k < n, Can52 vals[k]!.2
  mul_inv : ∀ k < n, mul 52 vals[k]!.1 vals[k]!.2 = idM 52
  fst_pk : ∀ k < n, F.getD k 0 = pk52 vals[k]!.1
  snd_pk : ∀ k < n, mulS (F.getD k 0) (I.getD k 0) = idS → I.getD k 0 = pk52 vals[k]!.2

theorem F42NodeRel.ref_spec {F I : List ℕ} {vals : Array Pair} {n : ℕ} (h : F42NodeRel F I vals n)
    {c : ℕ} (hc : refOK F I n c = true) :
    Can52 (refVal vals (refOfCode c)).1 ∧ Can52 (refVal vals (refOfCode c)).2 ∧
      mul 52 (refVal vals (refOfCode c)).1 (refVal vals (refOfCode c)).2 = idM 52 ∧
      mul 52 (refVal vals (refOfCode c)).2 (refVal vals (refOfCode c)).1 = idM 52 ∧
      refK F I c = pk52 (refVal vals (refOfCode c)).1 := by
  obtain ⟨hlt, hodd⟩ := (refOK_iff F I n c).1 hc
  rw [refVal_refOfCode, refK_eq]
  have h1 := h.can_fst (c / 2) hlt
  have h2 := h.can_snd (c / 2) hlt
  have h3 := h.mul_inv (c / 2) hlt
  have h4 := mul52_comm_of_inv h1 h2 h3
  have h5 := h.fst_pk (c / 2) hlt
  by_cases hc2 : c % 2 = 0
  · rw [if_pos hc2, if_pos hc2]
    exact ⟨h1, h2, h3, h4, h5⟩
  · rw [if_neg hc2, if_neg hc2]
    have h6 := h.snd_pk (c / 2) hlt (hodd (by omega))
    exact ⟨h2, h1, h4, h3, h6⟩

theorem F42NodeRel.ref_xor {F I : List ℕ} {vals : Array Pair} {n : ℕ} (h : F42NodeRel F I vals n)
    {c : ℕ} (hc : refOK F I n c = true) (hc' : refOK F I n (Nat.xor c 1) = true) :
    refK F I (Nat.xor c 1) = pk52 (refVal vals (refOfCode c)).2 := by
  have h1 := (h.ref_spec hc').2.2.2.2
  rw [h1]
  congr 1
  rw [refVal_refOfCode, refVal_refOfCode]
  have hd : Nat.xor c 1 / 2 = c / 2 := by
    have := Nat.xor_div_two (a := c) (b := 1)
    simpa using this
  have hm : Nat.xor c 1 % 2 = 1 ↔ ¬ c % 2 = 1 := by
    have := Nat.xor_mod_two_eq_one (a := c) (b := 1)
    simpa using this
  by_cases hc2 : c % 2 = 0
  · have h' : ¬ (Nat.xor c 1 % 2 = 0) := by
      have := hm.2 (by omega)
      omega
    rw [if_neg h', if_pos hc2, hd]
    rfl
  · have h' : Nat.xor c 1 % 2 = 0 := by
      have : ¬ (Nat.xor c 1 % 2 = 1) := fun hh => (hm.1 hh) (by omega)
      omega
    rw [if_pos h', if_neg hc2, hd]
    rfl

theorem nodeRel_start {cA cB F I : List ℕ} (hst : startK cA cB F I = true)
    (hI0 : wfS (I.getD 0 0) = true) (hI1 : wfS (I.getD 1 0) = true) :
    F42NodeRel F I (f42Init (strOf cA) (strOf cB)) 2 := by
  obtain ⟨hF0, hF1, hAA, hBBB, hAI, hBI⟩ := startK_iff.1 hst
  simp only [decodeK_eq, ← strOf_eq_strL] at hF0 hF1 hAA hBBB hAI hBI
  have hCA : Can52 (rowsOf 52 (strOf cA)) := can52_rowsOf _
  have hCB : Can52 (rowsOf 52 (strOf cB)) := can52_rowsOf _
  have hAA' : mul 52 (rowsOf 52 (strOf cA)) (rowsOf 52 (strOf cA)) = idM 52 := by
    rw [mulS_pk52 hCA hCA, idS_eq] at hAA
    exact pk52_inj (can52_mul hCA hCA) can52_idM hAA
  have hBBB' : mul 52 (rowsOf 52 (strOf cB)) (mul 52 (rowsOf 52 (strOf cB)) (rowsOf 52 (strOf cB))) =
      idM 52 := by
    rw [mulS_pk52 hCB hCB, mulS_pk52 hCB (can52_mul hCB hCB), idS_eq] at hBBB
    exact pk52_inj (can52_mul hCB (can52_mul hCB hCB)) can52_idM hBBB
  have e0 : (f42Init (strOf cA) (strOf cB))[0]! = (rowsOf 52 (strOf cA), rowsOf 52 (strOf cA)) := rfl
  have e1 : (f42Init (strOf cA) (strOf cB))[1]! =
      (rowsOf 52 (strOf cB), mul 52 (rowsOf 52 (strOf cB)) (rowsOf 52 (strOf cB))) := rfl
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    interval_cases k
    · rw [e0]; exact hCA
    · rw [e1]; exact hCB
  · intro k hk
    interval_cases k
    · rw [e0]; exact hCA
    · rw [e1]; exact can52_mul hCB hCB
  · intro k hk
    interval_cases k
    · rw [e0]; exact hAA'
    · rw [e1]; exact hBBB'
  · intro k hk
    interval_cases k
    · rw [e0]; exact hF0
    · rw [e1]; exact hF1
  · intro k hk
    interval_cases k
    · intro hm
      rw [e0]
      rw [hF0] at hm
      exact pk52_of_mulS_eq_idS hCA hCA hAA' hI0 hm
    · intro hm
      rw [e1]
      rw [hF1] at hm
      exact pk52_of_mulS_eq_idS hCB (can52_mul hCB hCB) hBBB' hI1 hm

theorem nodeRel_step {F I R : List ℕ} {vals : Array Pair} {t : ℕ}
    (h : F42NodeRel F I vals (t + 2)) (hins : insK F I R t = true)
    (hI : wfS (I.getD (t + 2) 0) = true) :
    F42NodeRel F I
      (slpStep vals (refOfCode (R.getD (2 * t) 0), refOfCode (R.getD (2 * t + 1) 0))) (t + 2 + 1) := by
  obtain ⟨hx, hy, hmul⟩ := (insK_iff F I R t).1 hins
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := h.ref_spec hx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := h.ref_spec hy
  have hstep : slpStep vals (refOfCode (R.getD (2 * t) 0), refOfCode (R.getD (2 * t + 1) 0)) =
      vals.push (mul 52 (refVal vals (refOfCode (R.getD (2 * t) 0))).1
          (refVal vals (refOfCode (R.getD (2 * t + 1) 0))).1,
        mul 52 (refVal vals (refOfCode (R.getD (2 * t + 1) 0))).2
          (refVal vals (refOfCode (R.getD (2 * t) 0))).2) := rfl
  rw [hstep]
  generalize refVal vals (refOfCode (R.getD (2 * t) 0)) = x at hx1 hx2 hx3 hx4 hx5 ⊢
  generalize refVal vals (refOfCode (R.getD (2 * t + 1) 0)) = y at hy1 hy2 hy3 hy4 hy5 ⊢
  have hP : Can52 (mul 52 x.1 y.1) := can52_mul hx1 hy1
  have hQ : Can52 (mul 52 y.2 x.2) := can52_mul hy2 hx2
  have hPQ : mul 52 (mul 52 x.1 y.1) (mul 52 y.2 x.2) = idM 52 := by
    rw [mul52_assoc hx1 hy1 hQ, ← mul52_assoc hy1 hy2 hx2, hy3, one_mul52 hx2, hx3]
  have hF : F.getD (t + 2) 0 = pk52 (mul 52 x.1 y.1) := by
    rw [← hmul, hx5, hy5]
    exact mulS_pk52 hx1 hy1
  have hsize : vals.size = t + 2 := h.size_eq
  have hpe : (vals.push (mul 52 x.1 y.1, mul 52 y.2 x.2))[t + 2]! =
      (mul 52 x.1 y.1, mul 52 y.2 x.2) := by
    have := push_getElem!_eq vals (mul 52 x.1 y.1, mul 52 y.2 x.2)
    rwa [hsize] at this
  refine ⟨by rw [Array.size_push, hsize], ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hk' : k < t + 2
    · rw [push_getElem!_lt vals _ (by omega)]
      exact h.can_fst k hk'
    · obtain rfl : k = t + 2 := by omega
      rw [hpe]
      exact hP
  · intro k hk
    by_cases hk' : k < t + 2
    · rw [push_getElem!_lt vals _ (by omega)]
      exact h.can_snd k hk'
    · obtain rfl : k = t + 2 := by omega
      rw [hpe]
      exact hQ
  · intro k hk
    by_cases hk' : k < t + 2
    · rw [push_getElem!_lt vals _ (by omega)]
      exact h.mul_inv k hk'
    · obtain rfl : k = t + 2 := by omega
      rw [hpe]
      exact hPQ
  · intro k hk
    by_cases hk' : k < t + 2
    · rw [push_getElem!_lt vals _ (by omega)]
      exact h.fst_pk k hk'
    · obtain rfl : k = t + 2 := by omega
      rw [hpe]
      exact hF
  · intro k hk hm
    by_cases hk' : k < t + 2
    · rw [push_getElem!_lt vals _ (by omega)]
      exact h.snd_pk k hk' hm
    · obtain rfl : k = t + 2 := by omega
      rw [hpe]
      rw [hF] at hm
      exact pk52_of_mulS_eq_idS hP hQ hPQ hI hm

theorem slpVals_nodeRel {pA pB slp : String} {cA cB cS Rc F I : List ℕ} {nI : ℕ}
    (hA : pA = strOf cA) (hB : pB = strOf cB) (hS : slp = strOf cS) (hfmt : fmtK cS = true)
    (hints : eqLN (intsK cS) Rc = true) (hst : startK cA cB F I = true)
    (hnI : nI = lenN Rc / 2) (hins : ∀ t < nI, insK F I Rc t = true)
    (hwI : ∀ k < nI + 2, wfS (I.getD k 0) = true) :
    F42NodeRel F I (slpValsOf pA pB slp) (nI + 2) := by
  have hN : nI = Rc.length / 2 := by rw [hnI, lenN_misc_eq]
  rw [slpValsOf_eq hS hfmt hints, ← hN]
  suffices H : ∀ t ≤ nI, F42NodeRel F I (f42Nodes (f42Init pA pB) Rc t) (t + 2) from H nI le_rfl
  intro t
  induction t with
  | zero =>
    intro _
    rw [f42Nodes_zero, hA, hB]
    exact nodeRel_start hst (hwI 0 (by omega)) (hwI 1 (by omega))
  | succ t ih =>
    intro ht
    rw [f42Nodes_succ]
    exact nodeRel_step (ih (by omega)) (hins t (by omega)) (hwI (t + 2) (by omega))

structure F42LiftRel (LF LI : List ℕ) (L : Array Pair) : Prop where
  can_fst : ∀ k < 48, Can52 L[k]!.1
  can_snd : ∀ k < 48, Can52 L[k]!.2
  fst_pk : ∀ k < 48, LF.getD k 0 = pk52 L[k]!.1
  snd_pk : ∀ k < 48, LI.getD k 0 = pk52 L[k]!.2

theorem liftsOf_getElem! {pA pB slp : String} {LR : List ℕ} {k : ℕ} (hk : k < LR.length) :
    (liftsOf pA pB slp (LR.map refOfCode))[k]! =
      refVal (slpValsOf pA pB slp) (refOfCode (LR.getD k 0)) := by
  unfold liftsOf
  simp [List.getD_eq_getElem?_getD, hk]

theorem liftRel_of_liftsK {pA pB slp : String} {F I LR LF LI : List ℕ} {nI : ℕ}
    (hN : F42NodeRel F I (slpValsOf pA pB slp) (nI + 2))
    (hl : liftsK F I LR LF LI (nI + 2) = true) :
    F42LiftRel LF LI (liftsOf pA pB slp (LR.map refOfCode)) := by
  obtain ⟨hlen, hall⟩ := liftsK_iff.1 hl
  have key : ∀ k < 48, (liftsOf pA pB slp (LR.map refOfCode))[k]! =
      refVal (slpValsOf pA pB slp) (refOfCode (LR.getD k 0)) := fun k hk =>
    liftsOf_getElem! (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨h1, h2, h3, h4⟩ := hall k hk
    rw [key k hk]
    exact (hN.ref_spec h1).1
  · intro k hk
    obtain ⟨h1, h2, h3, h4⟩ := hall k hk
    rw [key k hk]
    exact (hN.ref_spec h1).2.1
  · intro k hk
    obtain ⟨h1, h2, h3, h4⟩ := hall k hk
    rw [key k hk, h3]
    exact (hN.ref_spec h1).2.2.2.2
  · intro k hk
    obtain ⟨h1, h2, h3, h4⟩ := hall k hk
    rw [key k hk, h4]
    exact hN.ref_xor h1 h2

end CFSG.KS.PK

end
