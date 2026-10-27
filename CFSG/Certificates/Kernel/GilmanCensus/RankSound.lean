module

public import CFSG.Certificates.Kernel.GilmanCensus.LinAlgSound
import all Certificates.Data.Census

public section

namespace Certificates.GilmanCensusK

open Certificates.Census

@[expose] def LLI (R : Array (Array Int)) : List (List Int) := R.toList.map Array.toList

theorem getElem!_eq_getD_toListI (v : Array Int) (i : Nat) : v[i]! = v.toList.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
  cases v[i]? <;> rfl

theorem getRowI (R : Array (Array Int)) (i : Nat) : (R[i]!).toList = (LLI R).getD i [] := by
  rw [LLI, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList, getElem!_def]
  cases R[i]? <;> rfl

theorem getEntI (R : Array (Array Int)) (i j : Nat) :
    R[i]![j]! = ((LLI R).getD i []).getD j 0 := by
  rw [getElem!_eq_getD_toListI, getRowI]

theorem LLI_set (R : Array (Array Int)) (i : Nat) (a : Array Int) :
    LLI (R.set! i a) = (LLI R).set i a.toList := by
  rw [LLI, LLI, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, List.map_set]

theorem length_LLI (R : Array (Array Int)) : (LLI R).length = R.size := by
  simp [LLI]

theorem rows_key {α : Type} [Inhabited α] (p : Nat → α → Bool) (g : α → α) (R : Array α) :
    ∀ n a (S : Array α), a + n = R.size → S.size = R.size →
      (∀ i (hi : i < R.size), S[i]! = if i < a then (if p i R[i] = true then g R[i] else R[i])
        else R[i]) →
      (List.range' a n).foldl
        (fun S i => if p i S[i]! = true then S.set! i (g S[i]!) else S) S =
      R.mapIdx (fun i r => if p i r = true then g r else r) := by
  intro n
  induction n with
  | zero =>
    intro a S ha hs hS
    simp only [List.range'_zero, List.foldl_nil]
    apply Array.ext
    · simp [hs]
    · intro i h1 h2
      have := hS i (by omega)
      rw [getElem!_pos S i h1, if_pos (by omega)] at this
      rw [Array.getElem_mapIdx]
      exact this
  | succ n ih =>
    intro a S ha hs hS
    rw [List.range'_succ, List.foldl_cons]
    have hSa := hS a (by omega)
    rw [if_neg (by omega)] at hSa
    apply ih (a + 1) _ (by omega)
    · split <;> simp [hs]
    · intro i hi
      rw [hSa]
      by_cases hia : i = a
      · subst hia
        by_cases hp : p i R[i] = true
        · rw [if_pos hp, Array.set!_eq_setIfInBounds,
            getElem!_pos _ i (by simp [hs]; omega), Array.getElem_setIfInBounds_self]
          simp [hp]
        · rw [if_neg hp]
          have := hS i hi
          simp [hp, this]
      · have e : (if p a R[a] = true then S.set! a (g R[a]) else S)[i]! = S[i]! := by
          split
          · rw [Array.set!_eq_setIfInBounds, getElem!_pos _ i (by simp [hs]; omega),
              getElem!_pos S i (by omega), Array.getElem_setIfInBounds_ne (by omega) (Ne.symm hia)]
          · rfl
        rw [e, hS i hi]
        by_cases hlt : i < a
        · have h2 : i < a + 1 := by omega
          simp only [hlt, h2, ↓reduceIte]
        · have h2 : ¬i < a + 1 := by omega
          simp only [hlt, h2, ↓reduceIte]

theorem foldl_congr_mem {β : Type} (f g : β → Nat → β) :
    ∀ (l : List Nat) (s : β), (∀ x ∈ l, ∀ s, f s x = g s x) → l.foldl f s = l.foldl g s
  | [], _, _ => rfl
  | x :: l, s, h => by
    rw [List.foldl_cons, List.foldl_cons, h x (by simp) s]
    exact foldl_congr_mem f g l _ (fun y hy => h y (by simp [hy]))

theorem foldl_rows_from {α : Type} [Inhabited α] (p : α → Bool) (g : α → α) (R : Array α)
    (a n : Nat) (h : a + n = R.size) :
    (List.range' a n).foldl (fun S i => if p S[i]! = true then S.set! i (g S[i]!) else S) R =
      R.mapIdx (fun i r => if (decide (a ≤ i) && p r) = true then g r else r) := by
  rw [foldl_congr_mem _ (fun S i => if (decide (a ≤ i) && p S[i]!) = true then
    S.set! i (g S[i]!) else S) _ _ (fun x hx s => by
      have : a ≤ x := (List.mem_range'_1.mp hx).1
      simp [this])]
  exact rows_key (fun i r => decide (a ≤ i) && p r) g R n a R h rfl (fun i hi => by
    rw [getElem!_pos R i hi]
    by_cases hia : i < a
    · have : ¬a ≤ i := by omega
      simp [hia, this]
    · simp [hia])

@[expose] def rqRow (n : Nat) (rowr rowi : Array Int) (j : Nat) : Array Int :=
  let nr : Array Int := Array.ofFn (n := n) fun t => rowr[j]! * rowi[t.val]! - rowi[j]! * rowr[t.val]!
  let g := nr.foldl (fun g x => Nat.gcd g x.natAbs) 0
  if g > 1 then nr.map (· / (g : Int)) else nr

@[expose] def rqM (n m j : Nat) (s : Array (Array Int) × Nat) : Array (Array Int) × Nat :=
  if s.2 < m then
    match (List.range' s.2 (m - s.2)).find? (fun i => s.1[i]![j]! != 0) with
    | none => s
    | some qq =>
      let R1 := (s.1.set! s.2 s.1[qq]!).set! qq s.1[s.2]!
      ((List.range' (s.2 + 1) (m - (s.2 + 1))).foldl (fun S i =>
        if (S[i]![j]! != 0) = true then S.set! i (rqRow n R1[s.2]! S[i]! j) else S) R1, s.2 + 1)
  else s

theorem rankQ_fold (rows : Array (Array Int)) :
    rankQ rows = if rows.size = 0 then 0 else
      ((List.range' 0 rows[0]!.size).foldl (fun s j => rqM rows[0]!.size rows.size j s)
        (rows, 0)).2 := by
  unfold rankQ
  by_cases h0 : rows.size = 0
  · simp [h0]
  · have h0' : (rows.size == 0) = false := by simpa using h0
    simp only [h0', h0, Bool.false_eq_true, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    rw [forIn_yield (fun s j => rqM rows[0]!.size rows.size j s)]
    · rfl
    · intro j s
      unfold rqM
      split
      · rw [forIn_yield (fun q i => if (q.isNone && s.1[i]![j]! != 0) = true then some i else q)
          _ (fun i q => by split <;> rfl), foldl_first, idBind]
        cases List.find? (fun i => s.1[i]![j]! != 0) (List.range' s.2 (rows.size - s.2)) with
        | none => rfl
        | some qq =>
          dsimp only
          rw [idBind, forIn_ifs]
          rfl
      · rfl

@[expose] def rqRowL (rr : List Int) (j : Nat) (ri : List Int) : List Int :=
  let c := ri.getD j 0
  if c != 0 then
    let nr := List.zipWith (fun a b => rr.getD j 0 * a - c * b) ri rr
    let g := gcdL nr
    if g > 1 then nr.map (· / (g : Int)) else nr
  else ri

theorem rqRow_toList (n : Nat) (rowr rowi : Array Int) (j : Nat) (hr : rowr.size = n)
    (hi : rowi.size = n) :
    (rqRow n rowr rowi j).toList =
      (let nr := List.zipWith (fun a b => rowr.toList.getD j 0 * a - rowi.toList.getD j 0 * b)
          rowi.toList rowr.toList
        let g := gcdL nr
        if g > 1 then nr.map (· / (g : Int)) else nr) := by
  have hnr : (Array.ofFn (n := n) fun t => rowr[j]! * rowi[t.val]! - rowi[j]! * rowr[t.val]!).toList
      = List.zipWith (fun a b => rowr.toList.getD j 0 * a - rowi.toList.getD j 0 * b)
          rowi.toList rowr.toList := by
    apply List.ext_getElem
    · simp [hr, hi]
    · intro c h1 h2
      have hc : c < n := by simpa using h1
      simp only [Array.toList_ofFn, List.getElem_ofFn, List.getElem_zipWith]
      rw [getElem!_eq_getD_toListI, getElem!_eq_getD_toListI, getElem!_eq_getD_toListI,
        getElem!_eq_getD_toListI, getD_lt rowi.toList 0 (i := c) (by simp [hi, hc]),
        getD_lt rowr.toList 0 (i := c) (by simp [hr, hc])]
  unfold rqRow gcdL
  dsimp only
  rw [← Array.foldl_toList, hnr]
  split
  · rw [Array.toList_map, hnr]
  · exact hnr

theorem length_rqRowL (rr ri : List Int) (j n : Nat) (h1 : rr.length = n) (h2 : ri.length = n) :
    (rqRowL rr j ri).length = n := by
  unfold rqRowL
  dsimp only
  split
  · split <;> simp [h1, h2]
  · exact h2

theorem LLI_mapIdx (R : Array (Array Int)) (g : Nat → Array Int → Array Int)
    (g' : Nat → List Int → List Int)
    (h : ∀ i (hi : i < R.size), (g i R[i]).toList = g' i R[i].toList) :
    LLI (R.mapIdx g) = (LLI R).mapIdx g' := by
  apply List.ext_getElem
  · simp [LLI]
  · intro i h1 h2
    simp only [LLI, Array.toList_mapIdx, List.getElem_map, List.getElem_mapIdx]
    have hi : i < R.size := by simpa [LLI] using h1
    simp only [Array.getElem_toList]
    exact h i hi

theorem mapIdx_below {α : Type} (A B : List α) (x : α) (e : α → α) :
    (A ++ x :: B).mapIdx (fun i r => if decide (A.length + 1 ≤ i) = true then e r else r) =
      A ++ x :: B.map e := by
  rw [List.mapIdx_append, List.mapIdx_cons]
  congr 1
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      have : ¬A.length + 1 ≤ i := by simp at h1; omega
      simp [this]
  · congr 1
    · have : ¬A.length + 1 ≤ 0 + A.length := by omega
      simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte]
    · apply List.ext_getElem
      · simp
      · intro i h1 h2
        have : A.length + 1 ≤ i + 1 + A.length := by omega
        simp [this]

@[expose] def RQInv (n m : Nat) (s : Array (Array Int) × Nat) (st : List (List Int) × Nat) :
    Prop :=
  ∃ above : List (List Int), LLI s.1 = above ++ st.1 ∧ above.length = s.2 ∧ st.2 = s.2 ∧
    s.1.size = m ∧ ∀ r ∈ st.1, r.length = n

theorem rq_step (n m j : Nat) (s : Array (Array Int) × Nat) (st : List (List Int) × Nat)
    (h : RQInv n m s st) : RQInv n m (rqM n m j s) (rqStep j st) := by
  obtain ⟨R, k⟩ := s
  obtain ⟨rest, k'⟩ := st
  obtain ⟨A, hL, hk, hk', hm, hsz⟩ := h
  dsimp only at hL hk hk' hm hsz
  subst hk hk'
  have hlen : m = A.length + rest.length := by
    rw [← hm, ← length_LLI, hL, List.length_append]
  have hF : (List.range' A.length (m - A.length)).find? (fun i => R[i]![j]! != 0) =
      (rest.findIdx? (fun r => r.getD j 0 != 0)).map (A.length + ·) := by
    rw [show m - A.length = rest.length by omega]
    exact find_shift _ _ rest A (fun i => by rw [getEntI, hL])
  unfold rqM rqStep
  dsimp only
  rw [pickQ_spec]
  by_cases hlt : A.length < m
  · rw [if_pos hlt, hF]
    cases ht : rest.findIdx? (fun r => r.getD j 0 != 0) with
    | none => exact ⟨A, hL, rfl, rfl, hm, hsz⟩
    | some t =>
      have htl := findIdx?_lt _ rest t ht
      dsimp only [Option.map_some]
      have hne : rest ≠ [] := by
        intro h0
        simp [h0] at htl
      have hR1 : LLI ((R.set! A.length R[A.length + t]!).set! (A.length + t) R[A.length]!) =
          A ++ rest.getD t [] ::
            ((rest.set 0 (rest.getD t [])).set t (rest.getD 0 [])).tail := by
        rw [LLI_set, LLI_set, getRowI, getRowI, hL, getD_app, getD_app0, set_app0,
          set_app, swap_head rest t htl, List.tail_cons]
      generalize hR1d : (R.set! A.length R[A.length + t]!).set! (A.length + t) R[A.length]! = R1
        at hR1
      generalize hW : ((rest.set 0 (rest.getD t [])).set t (rest.getD 0 [])).tail = W at hR1 ⊢
      generalize hpd : rest.getD t [] = p at hR1 ⊢
      have hpmem : p ∈ rest := by
        rw [← hpd, getD_lt _ _ htl]
        exact List.getElem_mem htl
      have hWmem : ∀ r ∈ W, r ∈ rest := by
        intro r hr
        rw [← hW] at hr
        exact mem_swap rest t r (List.mem_of_mem_tail hr) htl
      have hR1k : (R1[A.length]!).toList = p := by
        rw [getRowI, hR1, getD_app0]
        rfl
      have hpl : p.length = n := hsz p hpmem
      have hrows : ∀ r ∈ A ++ p :: W, r ∈ A ∨ r.length = n := by
        intro r hr
        rcases List.mem_append.mp hr with h1 | h1
        · exact Or.inl h1
        · rcases List.mem_cons.mp h1 with h2 | h2
          · exact Or.inr (by rw [h2]; exact hpl)
          · exact Or.inr (hsz r (hWmem r h2))
      have hm1 : A.length + 1 + (m - (A.length + 1)) = R1.size := by
        rw [← length_LLI, hR1, List.length_append, List.length_cons]
        have : W.length + 1 = rest.length := by
          rw [← hW, List.length_tail, List.length_set, List.length_set]
          have := List.length_pos_iff.mpr hne
          omega
        omega
      have e := foldl_rows_from (fun (r : Array Int) => r[j]! != 0)
        (fun r => rqRow n R1[A.length]! r j) R1 (A.length + 1) (m - (A.length + 1)) hm1
      rw [e]
      have hLL := LLI_mapIdx R1 (fun i r => if (decide (A.length + 1 ≤ i) && r[j]! != 0) = true then
          rqRow n R1[A.length]! r j else r)
        (fun i r => if decide (A.length + 1 ≤ i) = true then rqRowL p j r
          else r) (fun i hi => by
            rw [getElem!_eq_getD_toListI]
            by_cases hc : (decide (A.length + 1 ≤ i) && R1[i].toList.getD j 0 != 0) = true
            · have hc2 : (R1[i].toList.getD j 0 != 0) = true := by
                simp only [Bool.and_eq_true] at hc
                exact hc.2
              have hiA : A.length + 1 ≤ i := by
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
                exact hc.1
              rw [if_pos hc, if_pos (by simpa using hiA)]
              have hri : R1[i].toList.length = n := by
                have hsz1 : R1.size = A.length + 1 + W.length := by
                  rw [← length_LLI, hR1]
                  simp
                  omega
                have hgi : R1[i].toList = (A ++ p :: W).getD i [] := by
                  rw [← hR1, ← getRowI, getElem!_pos R1 i hi]
                have hgi2 : (A ++ p :: W).getD i [] = W.getD (i - A.length - 1) [] := by
                  have e3 := getD_app A (p :: W) (i - A.length - 1 + 1) []
                  have e4 : A.length + (i - A.length - 1 + 1) = i := by omega
                  rw [e4, List.getD_cons_succ] at e3
                  exact e3
                rw [hgi, hgi2, getD_lt W [] (i := i - A.length - 1) (by omega)]
                exact hsz _ (hWmem _ (List.getElem_mem _))
              rw [rqRow_toList n _ _ j (by rw [← Array.length_toList, hR1k, hpl])
                (by simpa using hri), hR1k]
              unfold rqRowL
              dsimp only
              rw [if_pos hc2]
            · rw [if_neg hc]
              by_cases hiA : A.length + 1 ≤ i
              · rw [if_pos (by simpa using hiA)]
                have hc0 : ¬(R1[i].toList.getD j 0 != 0) = true := by simpa [hiA] using hc
                unfold rqRowL
                dsimp only
                rw [if_neg hc0]
              · rw [if_neg (by simpa using hiA)])
      rw [hR1, mapIdx_below] at hLL
      refine ⟨A ++ [p], ?_, ?_, rfl, ?_, ?_⟩
      · rw [hLL, List.append_assoc, List.singleton_append]
        rfl
      · simp
      · rw [Array.size_mapIdx, ← hm1]
        omega
      · intro r hr
        obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
        exact length_rqRowL p r' j n hpl (hsz r' (hWmem r' hr'))
  · rw [if_neg hlt]
    have h0 : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h0
    exact ⟨A, hL, rfl, rfl, hm, hsz⟩

theorem rq_fold (n m : Nat) : ∀ (l : List Nat) s st, RQInv n m s st →
    RQInv n m (l.foldl (fun s j => rqM n m j s) s) (l.foldl (fun st j => rqStep j st) st)
  | [], _, _, h => h
  | j :: l, s, st, h => rq_fold n m l _ _ (rq_step n m j s st h)

theorem rankQ_eq (rows : Array (Array Int)) (h : ∀ r ∈ rows.toList, r.size = rows[0]!.size) :
    rankQ rows = rankQK (LLI rows) := by
  rw [rankQ_fold]
  by_cases h0 : rows.size = 0
  · rw [if_pos h0]
    have : LLI rows = [] := by
      rw [← List.length_eq_zero_iff, length_LLI, h0]
    rw [this]
    rfl
  · rw [if_neg h0]
    obtain ⟨r0, tl, hrt⟩ : ∃ r0 tl, LLI rows = r0 :: tl := by
      cases hl : LLI rows with
      | nil =>
        exfalso
        have := length_LLI rows
        rw [hl] at this
        simp at this
        omega
      | cons r0 tl => exact ⟨r0, tl, rfl⟩
    have hr0 : r0 = rows[0]!.toList := by
      rw [getRowI, hrt]
      rfl
    have h0i : RQInv rows[0]!.size rows.size (rows, 0) (LLI rows, 0) := by
      refine ⟨[], by simp, rfl, rfl, rfl, ?_⟩
      intro r hr
      simp only [LLI, List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [h a ha]
    obtain ⟨-, -, -, hk, -, -⟩ := rq_fold _ _ (List.range' 0 rows[0]!.size) _ _ h0i
    rw [hrt, rankQK.eq_def]
    dsimp only
    rw [← hrt, hr0, Array.length_toList, List.range_eq_range']
    exact hk.symm

end Certificates.GilmanCensusK

end
