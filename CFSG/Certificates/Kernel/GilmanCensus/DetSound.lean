module

public import CFSG.Certificates.Kernel.GilmanCensus.RankSound
import all Certificates.Data.Census

public section

namespace Certificates.GilmanCensusK

open Certificates.Census

@[expose] def dElim (n k : Nat) (prev : Int) (rowk : Array Int) (A : Array (Array Int)) :
    Array (Array Int) :=
  (List.range' (k + 1) (n - (k + 1))).foldl (fun A i => A.set! i (Array.ofFn (n := n) fun j =>
    if j.val > k then (A[i]![j.val]! * rowk[k]! - A[i]![k]! * rowk[j.val]!) / prev
    else A[i]![j.val]!)) A

@[expose] def dBody (n k : Nat) (s : Option Int × Array (Array Int) × Int × Int) :
    Id (ForInStep (Option Int × Array (Array Int) × Int × Int)) :=
  let A := s.2.1
  let sign := s.2.2.1
  let prev := s.2.2.2
  if (A[k]![k]! == 0) = true then
    match (List.range' (k + 1) (n - (k + 1))).find? (fun i => A[i]![k]! != 0) with
    | none => pure (ForInStep.done (some 0, A, sign, prev))
    | some i =>
      let A1 := (A.set! k A[i]!).set! i A[k]!
      let A2 := dElim n k prev A1[k]! A1
      pure (ForInStep.yield (none, A2, -sign, A2[k]![k]!))
  else
    let A2 := dElim n k prev A[k]! A
    pure (ForInStep.yield (none, A2, sign, A2[k]![k]!))

theorem forIn_congr' {β : Type} {l : List Nat} {init : β} (F F' : Nat → β → Id (ForInStep β))
    (h : ∀ k s, F k s = F' k s) : forIn (m := Id) l init F = forIn (m := Id) l init F' := by
  have : F = F' := funext fun k => funext fun s => h k s
  rw [this]

theorem detInt_fold (M : Array (Array Int)) :
    detInt M = if M.size = 0 then 1 else
      (let r := Id.run (forIn (List.range' 0 (M.size - 1)) ((none : Option Int), M, (1 : Int),
          (1 : Int)) (fun k s => dBody M.size k s))
       match r.1 with
       | some x => x
       | none => r.2.2.1 * r.2.1[M.size - 1]![M.size - 1]!) := by
  unfold detInt
  by_cases h0 : M.size = 0
  · simp [h0]
  · have h0' : (M.size == 0) = false := by simpa using h0
    simp only [h0', h0, Bool.false_eq_true, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    rw [forIn_congr' _ (fun k s => dBody M.size k s) ?_]
    · rw [Id.run_bind]
      generalize (forIn (m := Id) (List.range' 0 (M.size - 1)) ((none : Option Int), M, (1 : Int),
        (1 : Int)) fun k s => dBody M.size k s) = r
      obtain ⟨o, A, sg, pv⟩ := r
      cases o <;> rfl
    · intro k s
      unfold dBody dElim
      dsimp only
      split
      · rw [forIn_yield (fun q i => if (q.isNone && s.2.1[i]![k]! != 0) = true then some i else q)
          _ (fun i q => by split <;> rfl), foldl_first, idBind]
        cases List.find? (fun i => s.2.1[i]![k]! != 0) (List.range' (k + 1) (M.size - (k + 1))) with
        | none => rfl
        | some i =>
          dsimp only
          rw [idBind, List.forIn_pure_yield_eq_foldl]
          rfl
      · rw [idBind, List.forIn_pure_yield_eq_foldl]
        rfl

@[expose] def dRowL (n k : Nat) (prev : Int) (rowk rowi : List Int) : List Int :=
  (List.range n).map fun j =>
    if j > k then (rowi.getD j 0 * rowk.getD k 0 - rowi.getD k 0 * rowk.getD j 0) / prev
    else rowi.getD j 0

theorem dRow_toList (n k : Nat) (prev : Int) (rowk rowi : Array Int) :
    (Array.ofFn (n := n) fun j =>
        if j.val > k then (rowi[j.val]! * rowk[k]! - rowi[k]! * rowk[j.val]!) / prev
        else rowi[j.val]!).toList = dRowL n k prev rowk.toList rowi.toList := by
  apply List.ext_getElem
  · simp [dRowL]
  · intro c h1 h2
    simp only [Array.toList_ofFn, List.getElem_ofFn, dRowL, List.getElem_map, List.getElem_range]
    simp only [getElem!_eq_getD_toListI]

theorem dElim_LLI (n k : Nat) (prev : Int) (rowk : Array Int) (A : Array (Array Int))
    (above below : List (List Int)) (x : List Int) (hA : LLI A = above ++ x :: below)
    (hk : above.length = k) (hn : A.size = n) :
    LLI (dElim n k prev rowk A) =
      above ++ x :: below.map (dRowL n k prev rowk.toList) := by
  have hsz : k + 1 + (n - (k + 1)) = A.size := by
    rw [← length_LLI, hA] at hn ⊢
    simp at hn ⊢
    omega
  have e := foldl_rows_from (fun _ => true) (fun r => Array.ofFn (n := n) fun j =>
      if j.val > k then (r[j.val]! * rowk[k]! - r[k]! * rowk[j.val]!) / prev else r[j.val]!)
    A (k + 1) (n - (k + 1)) hsz
  unfold dElim
  rw [foldl_congr_mem _ (fun S i => if (fun _ : Array Int => true) S[i]! = true then
    S.set! i ((fun r : Array Int => Array.ofFn (n := n) fun j =>
      if j.val > k then (r[j.val]! * rowk[k]! - r[k]! * rowk[j.val]!) / prev else r[j.val]!)
      S[i]!) else S) _ _ ?_, e]
  · rw [LLI_mapIdx A _ (fun i r => if decide (above.length + 1 ≤ i) = true then
        dRowL n k prev rowk.toList r else r) (fun i _ => by
      simp only [Bool.and_true, hk]
      split
      · exact dRow_toList n k prev rowk _
      · rfl), hA, mapIdx_below]
  · intro x _ s
    rfl

theorem detStep_none (n : Nat) : ∀ l : List Nat, l.foldl (fun st k => detStep n k st) none = none
  | [] => rfl
  | _ :: l => detStep_none n l

@[expose] def DInv (n k : Nat) (s : Option Int × Array (Array Int) × Int × Int)
    (rows : List (List Int)) (sign prev : Int) : Prop :=
  s.1 = none ∧ s.2.2.1 = sign ∧ s.2.2.2 = prev ∧ s.2.1.size = n ∧
    ∃ above, LLI s.2.1 = above ++ rows ∧ above.length = k

theorem d_step (n k : Nat) (hk : k + 1 < n) (s : Option Int × Array (Array Int) × Int × Int)
    (rows : List (List Int)) (sign prev : Int) (h : DInv n k s rows sign prev) :
    (∃ v, dBody n k s = ForInStep.done v ∧ v.1 = some 0 ∧ detStep n k (some (rows, sign, prev)) = none) ∨
    (∃ v rows' sign' prev', dBody n k s = ForInStep.yield v ∧
      detStep n k (some (rows, sign, prev)) = some (rows', sign', prev') ∧
      DInv n (k + 1) v rows' sign' prev') := by
  obtain ⟨o, A, sg, pv⟩ := s
  obtain ⟨ho, hs, hp, hn, above, hL, hab⟩ := h
  dsimp only at ho hs hp hn hL hab
  subst ho hs hp hab
  have hlen : above.length + rows.length = n := by
    rw [← hn, ← length_LLI, hL, List.length_append]
  obtain ⟨r0, tl, rfl⟩ : ∃ r0 tl, rows = r0 :: tl := by
    cases rows with
    | nil => simp at hlen; omega
    | cons r0 tl => exact ⟨r0, tl, rfl⟩
  have hr0 : (A[above.length]!).toList = r0 := by
    rw [getRowI, hL, getD_app0]
    rfl
  have hkk : A[above.length]![above.length]! = r0.getD above.length 0 := by
    rw [getElem!_eq_getD_toListI, hr0]
  have hL' : LLI A = (above ++ [r0]) ++ tl := by rw [hL]; simp
  have hF : (List.range' (above.length + 1) (n - (above.length + 1))).find?
      (fun i => A[i]![above.length]! != 0) =
      (tl.findIdx? (fun r => r.getD above.length 0 != 0)).map ((above ++ [r0]).length + ·) := by
    have e1 : n - (above.length + 1) = tl.length := by simp at hlen; omega
    have e2 : above.length + 1 = (above ++ [r0]).length := by simp
    rw [e1, e2]
    exact find_shift _ _ tl (above ++ [r0]) (fun i => by rw [getEntI, hL'])
  unfold dBody detStep
  dsimp only
  rw [hkk]
  by_cases hz : (r0.getD above.length 0 == 0) = true
  · rw [if_pos hz, if_pos hz, hF, findIn_spec]
    cases hu : tl.findIdx? (fun r => r.getD above.length 0 != 0) with
    | none =>
      left
      exact ⟨_, rfl, rfl, rfl⟩
    | some u =>
      right
      have hul := findIdx?_lt _ tl u hu
      dsimp only [Option.map_some]
      have hR1 : LLI ((A.set! above.length A[(above ++ [r0]).length + u]!).set!
          ((above ++ [r0]).length + u) A[above.length]!) =
          above ++ tl.getD u [] :: tl.set u r0 := by
        have e5 : (above ++ [r0]).length + u = above.length + (u + 1) := by simp; omega
        rw [LLI_set, LLI_set, getRowI, getRowI, hL, e5, getD_app, getD_app0, List.getD_cons_succ,
          List.getD_cons_zero, set_app0, set_app]
        rfl
      generalize hA1 : (A.set! above.length A[(above ++ [r0]).length + u]!).set!
          ((above ++ [r0]).length + u) A[above.length]! = A1 at hR1
      have hA1k : (A1[above.length]!).toList = tl.getD u [] := by
        rw [getRowI, hR1, getD_app0]
        rfl
      have hA1n : A1.size = n := by
        rw [← length_LLI, hR1]
        simp
        omega
      have hD := dElim_LLI n above.length pv A1[above.length]! A1 above (tl.set u r0)
        (tl.getD u []) hR1 rfl hA1n
      rw [hA1k] at hD
      refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · have : (dElim n above.length pv A1[above.length]! A1)[above.length]![above.length]! =
            (tl.getD u []).getD above.length 0 := by
          rw [getEntI, hD, getD_app0]
          rfl
        exact this
      · refine ⟨?_, above ++ [tl.getD u []], ?_, by simp⟩
        · rw [← length_LLI, hD]
          simp
          omega
        · rw [hD, List.append_assoc, List.singleton_append]
          rfl
  · have hz' : (r0.getD above.length 0 == 0) = false := by simpa using hz
    rw [if_neg hz, hz']
    right
    have hD := dElim_LLI n above.length pv A[above.length]! A above tl r0 hL rfl hn
    rw [hr0] at hD
    refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · have : (dElim n above.length pv A[above.length]! A)[above.length]![above.length]! =
          r0.getD above.length 0 := by
        rw [getEntI, hD, getD_app0]
        rfl
      exact this
    · refine ⟨?_, above ++ [r0], ?_, by simp⟩
      · rw [← length_LLI, hD]
        simp
        omega
      · rw [hD, List.append_assoc, List.singleton_append]
        rfl

theorem d_loop (n : Nat) : ∀ (len k : Nat) (s : Option Int × Array (Array Int) × Int × Int)
    (rows : List (List Int)) (sign prev : Int), k + len + 1 = n → DInv n k s rows sign prev →
    ((Id.run (forIn (List.range' k len) s (fun k s => dBody n k s))).1 = some 0 ∧
        (List.range' k len).foldl (fun st k => detStep n k st) (some (rows, sign, prev)) = none) ∨
    (∃ rows' sign' prev',
        (List.range' k len).foldl (fun st k => detStep n k st) (some (rows, sign, prev)) =
          some (rows', sign', prev') ∧
        DInv n (n - 1) (Id.run (forIn (List.range' k len) s (fun k s => dBody n k s)))
          rows' sign' prev') := by
  intro len
  induction len with
  | zero =>
    intro k s rows sign prev hk h
    right
    refine ⟨rows, sign, prev, rfl, ?_⟩
    have : n - 1 = k := by omega
    rw [this]
    exact h
  | succ len ih =>
    intro k s rows sign prev hk h
    rw [List.range'_succ, List.forIn_cons, List.foldl_cons]
    rcases d_step n k (by omega) s rows sign prev h with
      ⟨v, hv, hv1, ht⟩ | ⟨v, rows', sign', prev', hv, ht, hinv⟩
    · left
      rw [hv, ht, detStep_none]
      exact ⟨hv1, rfl⟩
    · rw [hv, ht]
      exact ih (k + 1) v rows' sign' prev' (by omega) hinv

theorem detInt_eq (M : Array (Array Int)) : detInt M = detIntK (LLI M) := by
  rw [detInt_fold]
  by_cases h0 : M.size = 0
  · rw [if_pos h0]
    have : LLI M = [] := by
      rw [← List.length_eq_zero_iff, length_LLI, h0]
    rw [this]
    rfl
  · rw [if_neg h0]
    have hn : (LLI M).length = M.size := length_LLI M
    have h0' : ((LLI M).length == 0) = false := by simpa [hn] using h0
    unfold detIntK
    dsimp only
    rw [h0', hn, List.range_eq_range']
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hinv : DInv M.size 0 ((none : Option Int), M, (1 : Int), (1 : Int)) (LLI M) 1 1 :=
      ⟨rfl, rfl, rfl, rfl, [], by simp, rfl⟩
    rcases d_loop M.size (M.size - 1) 0 _ (LLI M) 1 1 (by omega) hinv with
      ⟨h1, h2⟩ | ⟨rows', sign', prev', h2, ho, hs, hp, hsz, above, hL, hab⟩
    · rw [h1, h2]
    · rw [h2, ho]
      dsimp only
      rw [hs, getEntI, hL, ← hab, getD_app0]

end Certificates.GilmanCensusK

end
