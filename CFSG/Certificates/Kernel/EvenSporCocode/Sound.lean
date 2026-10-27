module

public import Certificates.Data.Kernel.EvenSporCocode.Defs

public section

namespace CFSG.KC.EvenSporCocode

open CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

theorem encT_cons (x : ℕ) (t : List ℕ) : encT (x :: t) = x + encT t * 32 := rfl

theorem encT_lt : ∀ t : List ℕ, (∀ x ∈ t, x < 32) → encT t < 32 ^ t.length
  | [], _ => by simp [encT]
  | x :: t, h => by
    have hx := h x (by simp)
    have ih := encT_lt t (fun y hy => h y (by simp [hy]))
    have h2 : (encT t + 1) * 32 ≤ 32 ^ t.length * 32 := Nat.mul_le_mul_right 32 ih
    rw [encT_cons, List.length_cons, pow_succ]
    rw [Nat.add_mul, one_mul] at h2
    omega

theorem encT_inj : ∀ s t : List ℕ, s.length = t.length → (∀ x ∈ s, x < 32) →
    (∀ x ∈ t, x < 32) → encT s = encT t → s = t
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | x :: s, y :: t, hl, hs, ht, h => by
    rw [encT_cons, encT_cons] at h
    have hx := hs x (by simp)
    have hy := ht y (by simp)
    have h1 : x = y := by omega
    have h2 : encT s = encT t := by omega
    rw [h1, encT_inj s t (by simpa using hl) (fun z hz => hs z (by simp [hz]))
      (fun z hz => ht z (by simp [hz])) h2]

theorem encAll_cons (t : List ℕ) (L : List (List ℕ)) :
    encAll (t :: L) = encT t + encAll L * 2 ^ 120 := by
  rw [← Nat.shiftLeft_eq]
  rfl

theorem fldE_encAll : ∀ (L : List (List ℕ)) (k : ℕ), (∀ t ∈ L, encT t < 2 ^ 120) →
    k < L.length → fldE (encAll L) k = encT (L.getD k [])
  | [], k, _, hk => absurd hk (by simp)
  | t :: L, 0, h, _ => by
    rw [fldE, encAll_cons, Nat.mul_zero, Nat.shiftRight_zero, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (h t (by simp))]
    rfl
  | t :: L, k + 1, h, hk => by
    have ih := fldE_encAll L k (fun s hs => h s (by simp [hs])) (by simpa using hk)
    have e : (encT t + encAll L * 2 ^ 120) >>> 120 = encAll L := by
      rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt (h t (by simp)), zero_add]
    rw [List.getD_cons_succ, ← ih, fldE, fldE, encAll_cons,
      show 120 * (k + 1) = 120 + 120 * k by ring, Nat.shiftRight_add, e]

@[expose] def ValidT (t : List ℕ) : Prop := t.length = 24 ∧ ∀ x ∈ t, x < 24

theorem validT_tmul {t u : List ℕ} (ht : ValidT t) (hu : ValidT u) : ValidT (tmul t u) := by
  refine ⟨by simp [tmul, hu.1], ?_⟩
  intro x hx
  simp only [tmul, List.mem_map] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have hjt : j < t.length := by rw [ht.1]; exact hu.2 j hj
  rw [List.getD_eq_getElem _ _ hjt]
  exact ht.2 _ (List.getElem_mem hjt)

theorem encT_lt_of_valid {t : List ℕ} (ht : ValidT t) : encT t < 2 ^ 120 := by
  have := encT_lt t (fun x hx => by have := ht.2 x hx; omega)
  rw [ht.1] at this
  simpa [show (32 : ℕ) ^ 24 = 2 ^ 120 by norm_num] using this

theorem encT_inj_valid {s t : List ℕ} (hs : ValidT s) (ht : ValidT t) (h : encT s = encT t) :
    s = t :=
  encT_inj s t (by rw [hs.1, ht.1]) (fun x hx => by have := hs.2 x hx; omega)
    (fun x hx => by have := ht.2 x hx; omega) h

abbrev idxOfList (P : List (List ℕ)) : Std.HashMap (List ℕ) ℕ :=
  P.foldl (fun (m : Std.HashMap (List ℕ) ℕ) t => m.insert t m.size) {}

theorem idxOfList_spec (P : List (List ℕ)) (hP : P.Nodup) :
    (idxOfList P).size = P.length ∧ (∀ x, x ∈ idxOfList P ↔ x ∈ P) ∧
      ∀ x, (idxOfList P).getD x 0 = if x ∈ P then P.idxOf x else 0 := by
  induction P using List.reverseRecOn with
  | nil => simp [idxOfList]
  | append_singleton P a ih =>
    have hP' : P.Nodup := hP.sublist (List.sublist_append_left P [a])
    have ha : a ∉ P := by
      intro h
      have := List.nodup_append.1 hP
      exact this.2.2 a h a (by simp) rfl
    obtain ⟨hs, hm, hg⟩ := ih hP'
    have hfold : idxOfList (P ++ [a]) = (idxOfList P).insert a (idxOfList P).size := by
      simp [idxOfList, List.foldl_append]
    have ham : a ∉ idxOfList P := fun h => ha ((hm a).1 h)
    rw [hfold]
    refine ⟨?_, ?_, ?_⟩
    · rw [Std.HashMap.size_insert, if_neg ham, hs, List.length_append, List.length_singleton]
    · intro x
      rw [Std.HashMap.mem_insert, hm, beq_iff_eq, List.mem_append, List.mem_singleton]
      tauto
    · intro x
      rw [Std.HashMap.getD_insert, hg, hs]
      by_cases hx : x = a
      · subst hx
        simp [ha, List.idxOf_append_of_notMem ha]
      · have hax : (a == x) = false := by simpa [beq_iff_eq] using Ne.symm hx
        rw [hax]
        simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton, hx,
          or_false]
        by_cases hxP : x ∈ P
        · rw [if_pos hxP, if_pos hxP, List.idxOf_append_of_mem hxP]
        · rw [if_neg hxP, if_neg hxP]

theorem rowsOf_toArray (L : List (List ℕ)) :
    rowsOf L.toArray = L.toArray.map fun t =>
      if isInv t then L.toArray.map fun u => (idxOfList L).getD (tmul t u) 0 else #[] := by
  simp only [rowsOf, idxOfList, List.foldl_toArray']

theorem getD_toArray {α : Type} (L : List α) (i : ℕ) (d : α) : L.toArray.getD i d = L.getD i d := by
  simp only [Array.getD, List.size_toArray, List.getElem_toArray]
  split <;> simp_all [List.getD_eq_getElem]

theorem getD_map_toArray {α β : Type} (L : List α) (f : α → β) (i : ℕ) (d : β) :
    (L.toArray.map f).getD i d = if h : i < L.length then f L[i] else d := by
  by_cases h : i < L.length
  · rw [Array.getD_eq_getD_getElem?, dif_pos h, Array.getElem?_map, List.getElem?_toArray,
      List.getElem?_eq_getElem h]
    rfl
  · rw [Array.getD_eq_getD_getElem?, dif_neg h, Array.getElem?_map, List.getElem?_toArray,
      List.getElem?_eq_none (by omega)]
    rfl

theorem lookup_rowsOf (L : List (List ℕ)) (hnd : L.Nodup) (i j : ℕ) :
    lookup (rowsOf L.toArray) i j =
      if i < L.length ∧ isInv (L.getD i []) = true ∧ j < L.length then
        (if tmul (L.getD i []) (L.getD j []) ∈ L then L.idxOf (tmul (L.getD i []) (L.getD j []))
          else 0)
      else 0 := by
  have hg := (idxOfList_spec L hnd).2.2
  rw [lookup, rowsOf_toArray, getD_map_toArray]
  by_cases hi : i < L.length
  · rw [dif_pos hi]
    by_cases hinv : isInv L[i] = true
    · rw [if_pos hinv, getD_map_toArray]
      by_cases hj : j < L.length
      · rw [dif_pos hj, hg, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj,
          if_pos (show i < L.length ∧ isInv L[i] = true ∧ j < L.length from ⟨hi, hinv, hj⟩)]
      · rw [dif_neg hj, if_neg (fun h => hj h.2.2)]
    · rw [if_neg hinv,
        if_neg (fun h => hinv (by rw [List.getD_eq_getElem _ _ hi] at h; exact h.2.1))]
      simp
  · rw [dif_neg hi, if_neg (fun h => hi h.1)]
    simp

theorem dig_encT : ∀ (t : List ℕ), (∀ x ∈ t, x < 32) → ∀ i, dig (encT t) i = t.getD i 0
  | [], _, i => by simp [dig, encT]
  | x :: t, h, 0 => by
    have hx := h x (by simp)
    rw [dig, encT_cons, Nat.mul_zero, Nat.shiftRight_zero, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hx]
    rfl
  | x :: t, h, i + 1 => by
    have hx := h x (by simp)
    have ih := dig_encT t (fun y hy => h y (by simp [hy])) i
    have e : (x + encT t * 32) >>> 5 = encT t := by
      rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 5 = 32 by norm_num,
        Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt hx, zero_add]
    rw [List.getD_cons_succ, ← ih, dig, dig, encT_cons,
      show 5 * (i + 1) = 5 + 5 * i by ring, Nat.shiftRight_add, e]

theorem tmulK_encT {t u : List ℕ} (ht : ValidT t) (hu : ValidT u) :
    tmulK (encT t) (encT u) = encT (tmul t u) := by
  have ht32 : ∀ x ∈ t, x < 32 := fun x hx => by have := ht.2 x hx; omega
  have hu32 : ∀ x ∈ u, x < 32 := fun x hx => by have := hu.2 x hx; omega
  rw [tmulK]
  congr 1
  apply List.ext_getElem
  · simp [tmul, hu.1]
  · intro n h1 h2
    simp only [List.length_map, List.length_range] at h1
    have hn : n < u.length := by rw [hu.1]; exact h1
    simp only [List.getElem_map, List.getElem_range, tmul, dig_encT t ht32, dig_encT u hu32,
      List.getD_eq_getElem _ _ hn]

theorem rowGo_spec {EP : ℕ} {RB : List ℕ} {i T : ℕ} :
    ∀ (Us : List ℕ) (j0 : ℕ), rowGo EP RB i T Us j0 = true →
      ∀ j < Us.length, tmulK T (Us.getD j 0) = fldE EP (lookK RB i (j0 + j))
  | [], _, _, j, hj => absurd hj (by simp)
  | U :: Us, j0, h, j, hj => by
    rw [rowGo, Bool.and_eq_true, beq_iff_eq] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := rowGo_spec Us (j0 + 1) h.2 j (by simpa using hj)
      rw [List.getD_cons_succ, this, show j0 + 1 + j = j0 + (j + 1) by omega]

theorem zeroSeg_spec {RB : List ℕ} {i : ℕ} (h : zeroSeg RB i = true) {j : ℕ} (hj : j < 1024) :
    lookK RB i j = 0 := by
  rw [zeroSeg, beq_iff_eq] at h
  rw [lookK, if_pos hj, show 10 * (1024 * (i % 32) + j) = 10240 * (i % 32) + 10 * j by ring,
    Nat.shiftRight_add]
  generalize RB.getD (i / 32) 0 >>> (10240 * (i % 32)) = Y at h ⊢
  have hd : 2 ^ (10 * j) * 2 ^ (10 + (10230 - 10 * j)) ∣ Y := by
    rw [← pow_add, show 10 * j + (10 + (10230 - 10 * j)) = 10240 by omega]
    exact Nat.dvd_of_mod_eq_zero h
  have h2 := Nat.dvd_div_of_mul_dvd hd
  rw [pow_add] at h2
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_zero_of_dvd (dvd_trans (by norm_num) (dvd_trans (dvd_mul_right _ _) h2))

theorem lookK_lt (RB : List ℕ) (i j : ℕ) : lookK RB i j < 1024 := by
  unfold lookK
  split
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num

theorem lookK_of_ge (RB : List ℕ) (hRB : RB.length = 32) {i : ℕ} (hi : 1024 ≤ i) (j : ℕ) :
    lookK RB i j = 0 := by
  unfold lookK
  rw [List.getD_eq_default _ _ (by rw [hRB]; omega)]
  simp

structure Hyps (L : List (List ℕ)) (K : List ℕ) (EP : ℕ) (RB : List ℕ) : Prop where
  len : L.length = 1024
  nodup : L.Nodup
  valid : ∀ t ∈ L, ValidT t
  kt : L.map encT = K
  ep : encAll L = EP
  rb : RB.length = 32
  rows : ∀ i < 1024, rowsAt EP RB L K i = true

theorem Hyps.validAt {L : List (List ℕ)} {K : List ℕ} {EP : ℕ} {RB : List ℕ} (h : Hyps L K EP RB)
    {k : ℕ} (hk : k < 1024) : ValidT (L.getD k []) := by
  rw [List.getD_eq_getElem _ _ (by rw [h.len]; exact hk)]
  exact h.valid _ (List.getElem_mem _)

theorem Hyps.kAt {L : List (List ℕ)} {K : List ℕ} {EP : ℕ} {RB : List ℕ} (h : Hyps L K EP RB)
    (k : ℕ) : K.getD k 0 = encT (L.getD k []) := by
  rw [← h.kt, show (0 : ℕ) = encT [] from rfl, List.getD_map]

theorem Hyps.fld {L : List (List ℕ)} {K : List ℕ} {EP : ℕ} {RB : List ℕ} (h : Hyps L K EP RB)
    {k : ℕ} (hk : k < 1024) : fldE EP k = encT (L.getD k []) := by
  rw [← h.ep]
  exact fldE_encAll L k (fun t ht => encT_lt_of_valid (h.valid t ht)) (by rw [h.len]; exact hk)

theorem Hyps.prod {L : List (List ℕ)} {K : List ℕ} {EP : ℕ} {RB : List ℕ} (h : Hyps L K EP RB)
    {i j : ℕ} (hi : i < 1024) (hinv : isInv (L.getD i []) = true) (hj : j < 1024) :
    tmul (L.getD i []) (L.getD j []) = L.getD (lookK RB i j) [] := by
  have hr := h.rows i hi
  rw [rowsAt, if_pos hinv] at hr
  have hKl : K.length = 1024 := by rw [← h.kt, List.length_map, h.len]
  have e1 := rowGo_spec K 0 hr j (by rw [hKl]; exact hj)
  rw [zero_add, h.kAt, h.kAt, tmulK_encT (h.validAt hi) (h.validAt hj),
    h.fld (lookK_lt RB i j)] at e1
  exact encT_inj_valid (validT_tmul (h.validAt hi) (h.validAt hj))
    (h.validAt (lookK_lt RB i j)) e1

theorem Hyps.lookup_eq {L : List (List ℕ)} {K : List ℕ} {EP : ℕ} {RB : List ℕ}
    (h : Hyps L K EP RB) :
    lookup (rowsOf L.toArray) = lookK RB := by
  funext i j
  rw [lookup_rowsOf L h.nodup, h.len]
  by_cases hi : i < 1024
  · by_cases hinv : isInv (L.getD i []) = true
    · by_cases hj : j < 1024
      · rw [if_pos ⟨hi, hinv, hj⟩, h.prod hi hinv hj]
        have hk := lookK_lt RB i j
        have hkL : lookK RB i j < L.length := by rw [h.len]; exact hk
        rw [List.getD_eq_getElem _ _ hkL, if_pos (List.getElem_mem hkL),
          List.Nodup.idxOf_getElem h.nodup _ hkL]
      · rw [if_neg (by omega)]
        unfold lookK
        rw [if_neg hj]
    · rw [if_neg (by tauto)]
      by_cases hj : j < 1024
      · have hr := h.rows i hi
        rw [rowsAt, if_neg hinv] at hr
        exact (zeroSeg_spec hr hj).symm
      · unfold lookK
        rw [if_neg hj]
  · rw [if_neg (by omega), lookK_of_ge RB h.rb (by omega)]

theorem cols_eq (L : List (List ℕ)) : colsTab L.toArray = colsK L := by
  funext i
  rw [colsTab, colsK, getD_toArray]

theorem Hyps.rowsOK {L : List (List ℕ)} {K : List ℕ} {EP : ℕ} {RB : List ℕ}
    (h : Hyps L K EP RB) :
    rowsOKWith L.toArray (rowsOf L.toArray) = true := by
  rw [rowsOKWith, h.lookup_eq, List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  rw [Bool.or_eq_true, Bool.not_eq_true']
  by_cases hinv : isInv (L.getD i []) = true
  · right
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    rw [getD_toArray, getD_toArray, getD_toArray, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, h.prod hi hinv hj]
    exact ⟨lookK_lt RB i j, rfl⟩
  · left
    rw [getD_toArray]
    simpa using hinv

theorem Hyps.dfsOK_eq {L : List (List ℕ)} {K : List ℕ} {EP : ℕ} {RB : List ℕ}
    (h : Hyps L K EP RB) :
    dfsOKWith L.toArray (rowsOf L.toArray) = dfsSub RB L (invsK L) (invsK L) := by
  rw [dfsOKWith, h.lookup_eq, cols_eq, dfsSub, invsK]
  simp only [getD_toArray]
  rfl

theorem all_of_blocks {l : List ℕ} {p : ℕ → Bool} {s n : ℕ} (hl : l.length ≤ s * n)
    (h : ∀ k < n, ((l.drop (s * k)).take s).all p = true) : l.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, zero_mul] at hl
      omega
    · exact h0
  have hk : i / s < n := by
    rw [Nat.div_lt_iff_lt_mul hs]
    rw [mul_comm] at hl
    omega
  have hb := List.all_eq_true.1 (h (i / s) hk)
  apply hb
  have hmod : i % s < s := Nat.mod_lt _ hs
  have hlt : s * (i / s) + i % s = i := Nat.div_add_mod i s
  rw [List.mem_iff_getElem]
  refine ⟨i % s, ?_, ?_⟩
  · simp only [List.length_take, List.length_drop]
    omega
  · simp only [List.getElem_take, List.getElem_drop, hlt]

theorem closeRow_spec {EP CB : ℕ} {l : List ℕ} {i : ℕ} :
    ∀ (gs : List (List ℕ)) (m0 : ℕ), closeRow EP CB l i gs m0 = true →
      ∀ m < gs.length, encT (tmul l (gs.getD m [])) = fldE EP (fldC CB (10 * i + (m0 + m)))
  | [], _, _, m, hm => absurd hm (by simp)
  | g :: gs, m0, h, m, hm => by
    rw [closeRow, Bool.and_eq_true, beq_iff_eq] at h
    cases m with
    | zero => simpa using h.1
    | succ m =>
      have := closeRow_spec gs (m0 + 1) h.2 m (by simpa using hm)
      rw [List.getD_cons_succ, this, show m0 + 1 + m = m0 + (m + 1) by omega]

theorem closeGo_spec {EP CB : ℕ} {gs : List (List ℕ)} :
    ∀ (ls : List (List ℕ)) (i0 : ℕ), closeGo EP CB gs ls i0 = true →
      ∀ i < ls.length, closeRow EP CB (ls.getD i []) (i0 + i) gs 0 = true
  | [], _, _, i, hi => absurd hi (by simp)
  | l :: ls, i0, h, i, hi => by
    rw [closeGo, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := closeGo_spec ls (i0 + 1) h.2 i (by simpa using hi)
      rw [List.getD_cons_succ, ← show i0 + 1 + i = i0 + (i + 1) by omega]
      exact this

theorem fldC_lt (CB p : ℕ) : fldC CB p < 1024 := Nat.mod_lt _ (by norm_num)

theorem validB_iff (t : List ℕ) : validB t = true ↔ ValidT t := by
  simp [validB, ValidT]

theorem spanOK_of {gs : List (List ℕ)} {EP CB : ℕ} (hlen : (span gs).length = 1024)
    (hnd : ((span gs).map encT).Nodup) (hval : ∀ t ∈ span gs, ValidT t)
    (hgs : ∀ g ∈ gs, ValidT g) (hep : encAll (span gs) = EP)
    (hcl : closeGo EP CB gs (span gs) 0 = true) : spanOK 1024 gs = true := by
  have hvalAt : ∀ k < 1024, ValidT ((span gs).getD k []) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hk)]
    exact hval _ (List.getElem_mem _)
  have hfld : ∀ k < 1024, fldE EP k = encT ((span gs).getD k []) := fun k hk => by
    rw [← hep]
    exact fldE_encAll _ k (fun t ht => encT_lt_of_valid (hval t ht)) (by rw [hlen]; exact hk)
  rw [spanOK, decide_eq_true_eq]
  refine ⟨hlen, List.Nodup.of_map _ hnd, ?_⟩
  intro l hl g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hg
  have hr := closeGo_spec (span gs) 0 hcl i hi
  rw [Nat.zero_add] at hr
  have e := closeRow_spec gs 0 hr m hm
  rw [Nat.zero_add, List.getD_eq_getElem _ _ hm, hfld _ (fldC_lt _ _)] at e
  rw [List.getD_eq_getElem _ _ hi] at e
  have e2 := encT_inj_valid (validT_tmul (hval _ (List.getElem_mem hi))
    (hgs _ (List.getElem_mem hm))) (hvalAt _ (fldC_lt _ _)) e
  rw [e2, List.getD_eq_getElem _ _ (by rw [hlen]; exact fldC_lt _ _)]
  exact List.getElem_mem _

theorem checks_of {gs LT : List (List ℕ)} {K : List ℕ} {EP CB : ℕ} {RB : List ℕ}
    (hLT : span gs = LT) (hlen : LT.length = 1024) (hnd : K.Nodup)
    (hval : LT.all validB = true) (hgs : gs.all validB = true) (hkt : LT.map encT = K)
    (hep : encAll LT = EP) (hrb : RB.length = 32) (hrows : ∀ i < 1024, rowsAt EP RB LT K i = true)
    (hcl : closeGo EP CB gs LT 0 = true) (hdfs : dfsSub RB LT (invsK LT) (invsK LT) = true) :
    spanOK 1024 gs = true ∧ rowsOKWith (tabsArr gs) (rowsOf (tabsArr gs)) = true ∧
      dfsOKWith (tabsArr gs) (rowsOf (tabsArr gs)) = true := by
  have hv : ∀ t ∈ LT, ValidT t := fun t ht => (validB_iff t).1 (List.all_eq_true.1 hval t ht)
  have hg : ∀ g ∈ gs, ValidT g := fun g hg => (validB_iff g).1 (List.all_eq_true.1 hgs g hg)
  have hndL : LT.Nodup := List.Nodup.of_map encT (by rw [hkt]; exact hnd)
  have h : Hyps LT K EP RB := ⟨hlen, hndL, hv, hkt, hep, hrb, hrows⟩
  have htabs : tabsArr gs = LT.toArray := by rw [tabsArr, hLT]
  refine ⟨?_, ?_, ?_⟩
  · subst hLT
    exact spanOK_of hlen (by rw [hkt]; exact hnd) hv hg hep hcl
  · rw [htabs]
    exact h.rowsOK
  · rw [htabs, h.dfsOK_eq]
    exact hdfs

theorem dfsSub_of_blocks {RB : List ℕ} {L : List (List ℕ)} {cands : List ℕ} {s n : ℕ}
    (hl : cands.length ≤ s * n)
    (h : ∀ k < n, dfsSub RB L cands ((cands.drop (s * k)).take s) = true) :
    dfsSub RB L cands cands = true :=
  all_of_blocks hl h

theorem testBit_eq_mod (x i : ℕ) : x.testBit i = decide ((x >>> i) % 2 = 1) := by
  rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]

theorem landBit (x i : ℕ) : Nat.land (Nat.shiftRight x i) 1 = if x.testBit i then 1 else 0 := by
  have e : Nat.land (Nat.shiftRight x i) 1 = (x >>> i) % 2 := Nat.and_one_is_mod _
  rw [e, testBit_eq_mod]
  rcases Nat.mod_two_eq_zero_or_one (x >>> i) with h | h <;> simp [h]

theorem planeK_bit (hP : planesB = true) {j m : ℕ} (hj : j < 12) (hm : m < 4096) :
    (planeK j).testBit m = m.testBit j := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 hP j (List.mem_range.2 hj)) m
    (List.mem_range.2 hm)
  rw [Nat.beq_eq, landBit, landBit] at h
  cases h1 : (planeK j).testBit m <;> cases h2 : m.testBit j <;> simp [h1, h2] at h ⊢

theorem imgPl_bit (hP : planesB = true) (k : ℕ) {m : ℕ} (hm : m < 4096) :
    ∀ (cs : List ℕ) (j : ℕ), j + cs.length ≤ 12 →
      (imgPl k j cs).testBit m = (xorImg cs (m >>> j)).testBit k
  | [], j, _ => by simp [imgPl, xorImg]
  | c :: cs, j, h => by
    have hl : j + 1 + cs.length ≤ 12 := by simp only [List.length_cons] at h; omega
    have hj : j < 12 := by omega
    rw [imgPl, xorImg, Nat.testBit_xor, Nat.testBit_xor, imgPl_bit hP k hm cs (j + 1) hl,
      ← Nat.shiftRight_succ]
    have hb := testBit_eq_mod m j
    have key : (bif c.testBit k then planeK j else 0).testBit m =
        (if (m >>> j) % 2 = 1 then c else 0).testBit k := by
      cases hc : c.testBit k <;> by_cases hmj : (m >>> j) % 2 = 1 <;>
        simp [hc, hmj, planeK_bit hP hj hm, hb]
    rw [key]

theorem xorImg_lt : ∀ (cs : List ℕ) (m : ℕ), (∀ x ∈ cs, x < 4096) → xorImg cs m < 4096
  | [], _, _ => by simp [xorImg]
  | c :: cs, m, h => by
    rw [xorImg]
    have h1 : (if m % 2 = 1 then c else 0) < 2 ^ 12 := by
      split
      · exact h c (by simp)
      · norm_num
    exact Nat.xor_lt_two_pow h1 (xorImg_lt cs (m / 2) fun x hx => h x (by simp [hx]))

theorem foldr_bit (f g : ℕ → ℕ) (m : ℕ) : ∀ ks : List ℕ,
    (ks.foldr (fun k acc => (f k ^^^ g k) ||| acc) 0).testBit m = false ↔
      ∀ k ∈ ks, (f k).testBit m = (g k).testBit m
  | [] => by simp
  | k :: ks => by
    rw [List.foldr_cons, Nat.testBit_or, Nat.testBit_xor, Bool.or_eq_false_iff, foldr_bit f g m ks,
      List.forall_mem_cons]
    cases (f k).testBit m <;> cases (g k).testBit m <;> simp

theorem movedK_bit (hP : planesB = true) (cs : List ℕ) (hl : cs.length = 12)
    (hc : ∀ x ∈ cs, x < 4096) {m : ℕ} (hm : m < 4096) :
    (movedK cs).testBit m = false ↔ xorImg cs m = m := by
  rw [movedK, foldr_bit]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 12
    · have := h i (List.mem_range.2 hi)
      rw [imgPl_bit hP i hm cs 0 (by omega), Nat.shiftRight_zero, planeK_bit hP hi hm] at this
      exact this
    · have h4096 : (4096 : ℕ) ≤ 2 ^ i := by
        calc (4096 : ℕ) = 2 ^ 12 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (xorImg_lt cs m hc) h4096),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hm h4096)]
  · intro e k hk
    have hk' := List.mem_range.1 hk
    rw [imgPl_bit hP k hm cs 0 (by omega), Nat.shiftRight_zero, planeK_bit hP hk' hm, e]

theorem strictL_eq (y : ℕ) (k : ℕ → List ℕ) : strictL y k = k y := by
  cases y <;> rfl

theorem extFK_eq (hP : planesB = true) (cols : ℕ → List ℕ)
    (hc : ∀ c, (cols c).length = 12 ∧ ∀ x ∈ cols c, x < 4096) (F : List ℕ)
    (hF : ∀ m ∈ F, m < 4096) (c : ℕ) : extFK cols F c = extF cols F c := by
  rw [extFK, strictL_eq]
  unfold extF
  apply List.filter_congr
  intro m hmF
  have hm := hF m hmF
  have hmv := movedK_bit hP (cols c) (hc c).1 (hc c).2 hm
  rw [landBit]
  cases hb : (movedK (cols c)).testBit m
  · rw [hmv.1 hb]
    simp
  · have hne : xorImg (cols c) m ≠ m := fun e => by
      rw [hmv.2 e] at hb
      exact Bool.false_ne_true hb
    have e1 : (if true = true then 1 else 0 : ℕ).beq 0 = false := rfl
    rw [e1]
    simp [hne]

theorem dfsK_eq (hP : planesB = true) (mulIdx : ℕ → ℕ → ℕ) (cols : ℕ → List ℕ)
    (hc : ∀ c, (cols c).length = 12 ∧ ∀ x ∈ cols c, x < 4096) :
    ∀ (n : ℕ) (V F cand : List ℕ), (∀ m ∈ F, m < 4096) →
      dfsK mulIdx cols n V F cand = dfs mulIdx cols n V F cand
  | 0, _, _, _, _ => rfl
  | n + 1, V, F, cand, hF => by
    rw [dfsK, dfs]
    unfold childrenK children
    refine congrArg (fun x => decide (V.length * F.length ≤ 2 ^ 11) && cand.all x)
      (funext fun c => ?_)
    beta_reduce
    have hF' : ∀ m ∈ extF cols F c, m < 4096 := fun m hm => by
      unfold extF at hm
      exact hF m (List.mem_filter.1 hm).1
    rw [extFK_eq hP cols hc F hF c, dfsK_eq hP mulIdx cols hc n _ _ _ hF']

theorem colsK_ok (L : List (List ℕ)) (c : ℕ) :
    (colsK L c).length = 12 ∧ ∀ x ∈ colsK L c, x < 4096 := by
  refine ⟨by simp [colsK, colsOfTab, pivotList], fun x hx => ?_⟩
  simp only [colsK, colsOfTab, List.mem_map] at hx
  obtain ⟨p, _, rfl⟩ := hx
  exact colMask_lt _

theorem dfsSubK_eq (hP : planesB = true) (RB : List ℕ) (L : List (List ℕ)) (cands sub : List ℕ) :
    dfsSubK RB L cands sub = dfsSub RB L cands sub := by
  have hF : ∀ m ∈ List.range 4096, m < 4096 := fun m hm => List.mem_range.1 hm
  unfold dfsSubK dfsSub childrenSubK childrenSub
  refine congrArg sub.all (funext fun c => ?_)
  beta_reduce
  have hF' : ∀ m ∈ extF (colsK L) (List.range 4096) c, m < 4096 := fun m hm => by
    unfold extF at hm
    exact hF m (List.mem_filter.1 hm).1
  rw [extFK_eq hP _ (colsK_ok L) _ hF c, dfsK_eq hP _ _ (colsK_ok L) 9 _ _ _ hF']

end CFSG.KC.EvenSporCocode
