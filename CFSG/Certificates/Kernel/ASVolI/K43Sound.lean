module

public import Certificates.Data.Kernel.ASVolI.K43K
public import CFSG.Certificates.Kernel.HMathieu.OrbSound
public import CFSG.Certificates.Kernel.MathieuAut.ColsKSound

public section

namespace CFSG.KS.ASVolI

open CFSG.ASVolI.K43Data CFSG.KC.HMathieu CFSG.KS.MathieuAut CFSG.Quasithin.H.Mathieu
  CFSG.Monster.Code

theorem k43_push_lt {α : Type} [Inhabited α] {a : Array α} {x : α} {i : ℕ} (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), Array.getElem_push_lt h, getElem!_pos a i h]

theorem k43_push_eq {α : Type} [Inhabited α] {a : Array α} {x : α} : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

theorem k43_getD_map {α β : Type} [Inhabited α] (f : α → β) {l : List α} {g : ℕ} (d : β)
    (hg : g < l.length) : (l.map f).getD g d = f l[g]! := by
  rw [List.getD_eq_getElem _ _ (by simpa using hg), List.getElem_map, getElem!_pos l g hg]

@[expose] def mInner (step : ℕ → ℕ → ℕ) (y h g : ℕ) (s : Std.HashSet ℕ × Array (ℕ × ℕ × ℕ)) :
    Id (ForInStep (Std.HashSet ℕ × Array (ℕ × ℕ × ℕ))) :=
  if (!s.1.contains (step g y)) = true then
    pure (ForInStep.yield (s.1.insert (step g y), s.2.push (step g y, h, g)))
  else pure (ForInStep.yield (s.1, s.2))

@[expose] def mOuter (step : ℕ → ℕ → ℕ) (ngen h : ℕ) (s : Std.HashSet ℕ × Array (ℕ × ℕ × ℕ)) :
    Id (ForInStep (Std.HashSet ℕ × Array (ℕ × ℕ × ℕ))) :=
  if h < s.2.size then
    pure (ForInStep.yield (Id.run (forIn (List.range' 0 ngen) (s.1, s.2) (mInner step s.2[h]!.1 h))))
  else pure (ForInStep.done (s.1, s.2))

theorem bfsTable_loops (step : ℕ → ℕ → ℕ) (ngen x0 cap : ℕ) :
    bfsTable step ngen x0 cap =
      (Id.run (forIn (List.range' 0 cap) ((∅ : Std.HashSet ℕ).insert x0, #[(x0, 0, 0)])
        (mOuter step ngen))).2 := by
  unfold bfsTable
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

def KRel (r : Std.HashSet ℕ × Array (ℕ × ℕ × ℕ)) (s : K43St) : Prop :=
  r.2 = s.1 ∧ ∀ k, s.2.mem k = r.1.contains k

variable {step step' : ℕ → ℕ → ℕ} {ngen : ℕ}

theorem inner_sim (hstep : ∀ g < ngen, ∀ y, step' g y = step g y) (y h : ℕ) :
    ∀ (L : List ℕ), (∀ g ∈ L, g < ngen) → ∀ r s, KRel r s →
      KRel (Id.run (forIn L r (mInner step y h))) (k43Inner step' y h L s) := by
  intro L
  induction L with
  | nil => intro _ r s R; exact R
  | cons g L ih =>
    intro hL r s R
    have hg := hL g List.mem_cons_self
    have hL' : ∀ g ∈ L, g < ngen := fun g' hg' => hL g' (List.mem_cons_of_mem g hg')
    rw [List.forIn_cons]
    unfold k43Inner
    rw [hstep g hg y, R.2]
    cases hc : r.1.contains (step g y)
    · simp only [mInner, hc, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
      refine ih hL' _ _ ⟨by rw [R.1], fun k => ?_⟩
      rw [KT.mem_ins, Std.HashSet.contains_insert, R.2, Bool.beq_comm]
    · simp only [mInner, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ih hL' _ _ R

theorem outer_sim (hstep : ∀ g < ngen, ∀ y, step' g y = step g y) :
    ∀ (f h : ℕ) r s, KRel r s →
      KRel (Id.run (forIn (List.range' h f) r (mOuter step ngen))) (k43Outer step' ngen f h s) := by
  intro f
  induction f with
  | zero => intro h r s R; exact R
  | succ f ih =>
    intro h r s R
    rw [List.range'_succ, List.forIn_cons]
    unfold k43Outer
    by_cases hh : h < s.1.size
    · have hh' : h < r.2.size := by rw [R.1]; exact hh
      simp only [mOuter, hh', hh, ↓reduceIte]
      refine ih (h + 1) _ _ ?_
      have := inner_sim hstep (s.1[h]!.1) h (List.range' 0 ngen)
        (fun g hg => by simpa using (List.mem_range'_1.1 hg).2) (r.1, r.2) s R
      rw [R.1] at this ⊢
      exact this
    · have hh' : ¬ h < r.2.size := by rw [R.1]; exact hh
      simp only [mOuter, hh', hh, ↓reduceIte]
      exact R

theorem bfsTable_eq_K (hstep : ∀ g < ngen, ∀ y, step' g y = step g y) (x0 cap : ℕ) :
    bfsTable step ngen x0 cap = (bfsTableK step' ngen x0 cap).1 := by
  rw [bfsTable_loops]
  refine (outer_sim hstep cap 0 _ _ ⟨rfl, fun k => ?_⟩).1
  rw [KT.mem_ins, Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
  simp [KT.mem, Bool.beq_comm]

structure KInv (step : ℕ → ℕ → ℕ) (ngen x0 : ℕ) (s : K43St) : Prop where
  pos : 0 < s.1.size
  root : s.1[0]!.1 = x0
  der : ∀ i < s.1.size, 0 < i →
    s.1[i]!.2.1 < i ∧ s.1[i]!.2.2 < ngen ∧ s.1[i]!.1 = step s.1[i]!.2.2 s.1[s.1[i]!.2.1]!.1
  mem : ∀ k, s.2.mem k = true ↔ k ∈ s.1.toList.map (·.1)
  nodup : (s.1.toList.map (·.1)).Nodup

theorem kinv_inner {x0 y h : ℕ} :
    ∀ (L : List ℕ), (∀ g ∈ L, g < ngen) → ∀ s, h < s.1.size → s.1[h]!.1 = y →
      KInv step ngen x0 s →
      KInv step ngen x0 (k43Inner step y h L s) ∧ h < (k43Inner step y h L s).1.size ∧
        (k43Inner step y h L s).1[h]!.1 = y := by
  intro L
  induction L with
  | nil => intro _ s hh hy I; exact ⟨I, hh, hy⟩
  | cons g L ih =>
    intro hL s hh hy I
    have hg := hL g List.mem_cons_self
    have hL' : ∀ g ∈ L, g < ngen := fun g' hg' => hL g' (List.mem_cons_of_mem g hg')
    unfold k43Inner
    cases hc : s.2.mem (step g y)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hnot : step g y ∉ s.1.toList.map (·.1) := fun hm => by
        rw [← I.mem, hc] at hm
        exact Bool.false_ne_true hm
      refine ih hL' _ (by simp; omega) (by rw [k43_push_lt hh, hy]) ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp
      · rw [k43_push_lt I.pos, I.root]
      · intro i hi h0
        simp only [Array.size_push] at hi
        rcases Nat.lt_or_ge i s.1.size with a | a
        · obtain ⟨d1, d2, d3⟩ := I.der i a h0
          rw [k43_push_lt a, k43_push_lt (by omega : s.1[i]!.2.1 < s.1.size)]
          exact ⟨d1, d2, d3⟩
        · have e : i = s.1.size := by omega
          subst e
          rw [k43_push_eq, k43_push_lt hh, hy]
          exact ⟨hh, hg, rfl⟩
      · intro k
        rw [KT.mem_ins, Bool.or_eq_true, beq_iff_eq, I.mem, Array.toList_push, List.map_append,
          List.mem_append, List.map_singleton, List.mem_singleton]
        exact Or.comm
      · rw [Array.toList_push, List.map_append, List.map_singleton]
        exact List.nodup_append.2 ⟨I.nodup, List.nodup_singleton _, fun a ha c hc' e => hnot (by
          rw [List.mem_singleton] at hc'
          rw [e, hc'] at ha
          exact ha)⟩
    · simp only [↓reduceIte]
      exact ih hL' s hh hy I

theorem kinv_outer {x0 : ℕ} :
    ∀ (f h : ℕ) s, KInv step ngen x0 s → KInv step ngen x0 (k43Outer step ngen f h s) := by
  intro f
  induction f with
  | zero => intro h s I; exact I
  | succ f ih =>
    intro h s I
    unfold k43Outer
    by_cases hh : h < s.1.size
    · rw [if_pos hh]
      exact ih _ _ (kinv_inner (List.range' 0 ngen)
        (fun g hg => by simpa using (List.mem_range'_1.1 hg).2) s hh rfl I).1
    · rw [if_neg hh]
      exact I

theorem kinv_bfsTableK (x0 cap : ℕ) : KInv step ngen x0 (bfsTableK step ngen x0 cap) := by
  refine kinv_outer cap 0 _ ⟨by simp, by simp, fun i hi h0 => ?_, fun k => ?_, by simp⟩
  · simp at hi
    omega
  · rw [KT.mem_ins]
    simp [KT.mem]

theorem lt_of_KInv {x0 B : ℕ} {s : K43St} (I : KInv step ngen x0 s) (h0 : x0 < B)
    (hB : ∀ g < ngen, ∀ y < B, step g y < B) : ∀ i < s.1.size, s.1[i]!.1 < B := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hz : i = 0
    · subst hz
      rw [I.root]
      exact h0
    · obtain ⟨d1, d2, d3⟩ := I.der i hi (by omega)
      rw [d3]
      exact hB _ d2 _ (ih _ d1 (by omega))

structure QRel (s : K43St) (h : ℕ) (q : QSt) : Prop where
  queue : (s.1.toList.drop h).map (·.1) = q.front ++ q.back.reverse
  cnt : q.cnt = s.1.size
  tree : ∀ k, q.tree.mem k = s.2.mem k

theorem qinner_sim {y h : ℕ} :
    ∀ (L : List ℕ) (s : K43St) (q : QSt), h + 1 ≤ s.1.size → QRel s (h + 1) q →
      QRel (k43Inner step y h L s) (h + 1) (qInner step y L q) ∧
        h + 1 ≤ (k43Inner step y h L s).1.size := by
  intro L
  induction L with
  | nil => intro s q hh R; exact ⟨R, hh⟩
  | cons g L ih =>
    intro s q hh R
    unfold k43Inner qInner
    rw [R.tree]
    by_cases hc : s.2.mem (step g y) = true
    · rw [if_pos hc, if_pos hc]
      exact ih s q hh R
    · rw [if_neg hc, if_neg hc]
      refine ih _ _ (by simp; omega) ⟨?_, ?_, fun k => ?_⟩
      · rw [Array.toList_push, List.drop_append_of_le_length (by simp; omega), List.map_append,
          R.queue, List.reverse_cons, List.append_assoc]
        rfl
      · rw [Array.size_push, R.cnt]
      · rw [KT.mem_ins, KT.mem_ins, R.tree]

theorem qouter_sim :
    ∀ (f h : ℕ) (s : K43St) (q : QSt), h ≤ s.1.size → QRel s h q →
      (qOuter step ngen f q).cnt = (k43Outer step ngen f h s).1.size ∧
        ∀ k, (qOuter step ngen f q).tree.mem k = (k43Outer step ngen f h s).2.mem k := by
  intro f
  induction f with
  | zero => intro h s q _ R; exact ⟨R.cnt, R.tree⟩
  | succ f ih =>
    intro h s q hh R
    rcases Nat.lt_or_ge h s.1.size with hlt | hge
    · have hd : (s.1.toList.drop h).map (·.1) = s.1[h]!.1 :: (s.1.toList.drop (h + 1)).map (·.1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hlt), List.map_cons, Array.getElem_toList,
          getElem!_pos s.1 h hlt]
      have hstep : ∀ (fr bk : List ℕ),
          (s.1.toList.drop (h + 1)).map (·.1) = fr ++ bk.reverse →
          (qOuter step ngen f (qInner step s.1[h]!.1 (List.range' 0 ngen) ⟨fr, bk, q.cnt, q.tree⟩)).cnt
              = (k43Outer step ngen (f + 1) h s).1.size ∧
            ∀ k, (qOuter step ngen f
              (qInner step s.1[h]!.1 (List.range' 0 ngen) ⟨fr, bk, q.cnt, q.tree⟩)).tree.mem k =
              (k43Outer step ngen (f + 1) h s).2.mem k := by
        intro fr bk he
        obtain ⟨R', hh'⟩ := qinner_sim (step := step) (y := s.1[h]!.1) (h := h)
          (List.range' 0 ngen) s ⟨fr, bk, q.cnt, q.tree⟩ (by omega) ⟨he, R.cnt, R.tree⟩
        rw [k43Outer, if_pos hlt]
        exact ih (h + 1) _ _ hh' R'
      obtain ⟨fr, bk, c, t⟩ := q
      have hq := R.queue
      rw [hd] at hq
      cases fr with
      | cons y fr' =>
        simp only [List.cons_append, List.cons.injEq] at hq
        obtain ⟨hy, hr⟩ := hq
        rw [qOuter, ← hy]
        exact hstep fr' bk hr
      | nil =>
        rw [List.nil_append] at hq
        cases hbk : bk.reverse with
        | nil => rw [hbk] at hq; cases hq
        | cons y fr' =>
          rw [hbk, List.cons.injEq] at hq
          obtain ⟨hy, hr⟩ := hq
          simp only [qOuter, hbk]
          rw [← hy]
          exact hstep fr' [] (by rw [hr, List.reverse_nil, List.append_nil])
    · have hiq : s.1.toList.drop h = [] := List.drop_eq_nil_of_le (by simp; omega)
      have hq := R.queue
      rw [hiq, List.map_nil] at hq
      obtain ⟨fr, bk, c, t⟩ := q
      have hfr : fr = [] := by
        cases fr with
        | nil => rfl
        | cons _ _ => simp at hq
      subst hfr
      have hbk : bk.reverse = [] := by
        rw [List.nil_append] at hq
        exact hq.symm
      have e1 : qOuter step ngen (f + 1) ⟨[], bk, c, t⟩ = ⟨[], bk, c, t⟩ := by
        simp only [qOuter, hbk]
      have e2 : k43Outer step ngen (f + 1) h s = s := by
        rw [k43Outer, if_neg (by omega)]
      rw [e1, e2]
      exact ⟨R.cnt, R.tree⟩

theorem bfsQ_eq (x0 cap : ℕ) :
    (bfsQ step ngen x0 cap).cnt = (bfsTableK step ngen x0 cap).1.size ∧
      ∀ k, (bfsQ step ngen x0 cap).tree.mem k = (bfsTableK step ngen x0 cap).2.mem k :=
  qouter_sim cap 0 _ _ (Nat.zero_le _) ⟨rfl, rfl, fun _ => rfl⟩

theorem derivOK_of_KInv (hstep : ∀ g < ngen, ∀ y, step' g y = step g y) {x0 : ℕ} {s : K43St}
    (I : KInv step' ngen x0 s) : derivOK step ngen x0 s.1 = true := by
  simp only [derivOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true]
  refine ⟨⟨I.pos, I.root⟩, fun i hi => ?_⟩
  by_cases h0 : i = 0
  · exact Or.inl h0
  · obtain ⟨d1, d2, d3⟩ := I.der i hi (by omega)
    exact Or.inr ⟨⟨d1, d2⟩, by rw [d3, hstep _ d2]⟩

theorem tabNodupLt_of_KInv {x0 B : ℕ} {s : K43St} (I : KInv step ngen x0 s) (h0 : x0 < B)
    (hB : ∀ g < ngen, ∀ y < B, step g y < B) : tabNodupLt B s.1 = true := by
  rw [tabNodupLt, decide_eq_true I.nodup, Bool.true_and, Array.all_eq_true]
  intro i hi
  have := lt_of_KInv I h0 hB i hi
  rw [getElem!_pos s.1 i hi] at this
  exact decide_eq_true this

theorem any_of_KInv {x0 : ℕ} {s : K43St} (I : KInv step ngen x0 s) (a : ℕ) :
    s.1.any (·.1 == a) = s.2.mem a := by
  rw [Bool.eq_iff_iff, I.mem, ← Array.any_toList, List.any_eq_true, List.mem_map]
  simp only [beq_iff_eq]

theorem octStepK_eq : ∀ g < gensK.length, ∀ y, octStepK g y = gStep gensK permM g y := by
  intro g hg y
  rw [octStepK, octCols, k43_getD_map _ _ hg]
  rfl

theorem inAutOK_eq_inAutK : inAutOK = inAutK := funext inAutOK_eq_K

theorem octOK_of_K (h : octOKK = true) : octOK () = true := by
  have I : KInv octStepK gensK.length e0mask (bfsTableK octStepK gensK.length e0mask 100000) :=
    kinv_bfsTableK _ _
  have e : octTab () = (bfsTableK octStepK gensK.length e0mask 100000).1 :=
    bfsTable_eq_K octStepK_eq _ _
  have hQ := (bfsQ_eq (step := octStepK) (ngen := gensK.length) e0mask 100000).2
  have hf : (fun a => if popc 24 a == 8 &&
        !((bfsTableK octStepK gensK.length e0mask 100000).1.any (·.1 == a)) then 1 else 0) =
      fun a => if popc 24 a == 8 &&
        !((bfsQ octStepK gensK.length e0mask 100000).tree.mem a) then 1 else 0 :=
    funext fun a => by rw [any_of_KInv I a, hQ a]
  have hm : octMiss (bfsTableK octStepK gensK.length e0mask 100000).1 =
      octMissK (bfsQ octStepK gensK.length e0mask 100000).tree := by
    unfold octMiss octMissK
    rw [hf]
  unfold octOK
  unfold octOKK at h
  dsimp only
  rw [e, derivOK_of_KInv octStepK_eq I, hm, inAutOK_eq_inAutK, Bool.and_true]
  exact h

theorem ptChainOK_of_K (h : ptChainK = true) : ptChainOK () = true := by
  unfold ptChainOK
  unfold ptChainK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨⟨⟨h1, h2⟩, h3⟩, fun i hi => ?_⟩
  obtain ⟨hg, hs⟩ := h4 i hi
  have hi6 : i < ptBase.length := by
    rw [beq_iff_eq.1 h1]
    exact List.mem_range.1 hi
  have hx0 : ptBase[i]! < 24 := by
    rw [getElem!_pos ptBase i hi6]
    exact of_decide_eq_true (h3 _ (List.getElem_mem hi6))
  have hB : ∀ g < (ptGens[i]!).length, ∀ y < 24, ptStep i g y < 24 := by
    intro g hgl y hy
    have hmem : (ptGens[i]!)[g]! ∈ ptGens[i]! := by
      rw [getElem!_pos (ptGens[i]!) g hgl]
      exact List.getElem_mem hgl
    exact of_decide_eq_true ((hg _ hmem).2 y (List.mem_range.2 hy))
  have I : KInv (ptStep i) (ptGens[i]!).length ptBase[i]!
      (bfsTableK (ptStep i) (ptGens[i]!).length ptBase[i]! 1000) := kinv_bfsTableK _ _
  have e : ptTab i = (bfsTableK (ptStep i) (ptGens[i]!).length ptBase[i]! 1000).1 :=
    bfsTable_eq_K (fun _ _ _ => rfl) _ _
  rw [e]
  refine ⟨⟨⟨fun g hg' => ⟨?_, (hg g hg').1.2⟩, derivOK_of_KInv (fun _ _ _ => rfl) I⟩,
    tabNodupLt_of_KInv I hx0 hB⟩, ?_⟩
  · rw [inAutOK_eq_K]
    exact (hg g hg').1.1
  · rw [← (bfsQ_eq (step := ptStep i) (ngen := (ptGens[i]!).length) ptBase[i]! 1000).1]
    exact hs

theorem vecChainOK_of_K (h : vecChainK = true) : vecChainOK () = true := by
  unfold vecChainOK
  unfold vecChainK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨⟨⟨h1, h2⟩, h3⟩, fun i hi => ?_⟩
  obtain ⟨hg, hs⟩ := h4 i hi
  have hi3 : i < vBase.length := by
    rw [beq_iff_eq.1 h1]
    exact List.mem_range.1 hi
  have hx0 : vBase[i]! < 2048 := by
    rw [getElem!_pos vBase i hi3]
    exact of_decide_eq_true (h3 _ (List.getElem_mem hi3))
  have hstep : ∀ g < (vGens[i]!).length, ∀ y, vStepK i g y = gStep (vGens[i]!) actC11 g y := by
    intro g hgl y
    have hmem : (vGens[i]!)[g]! ∈ vGens[i]! := by
      rw [getElem!_pos (vGens[i]!) g hgl]
      exact List.getElem_mem hgl
    have hsz := (hg _ hmem).1.1
    rw [vStepK, vCols, k43_getD_map _ _ hgl, gStep, actC11_eq_cols (by simpa using hsz)]
  have hB : ∀ g < (vGens[i]!).length, ∀ y < 2048, vStepK i g y < 2048 := fun g hgl y _ => by
    rw [hstep g hgl y]
    exact actC11_lt _ _
  have I : KInv (vStepK i) (vGens[i]!).length vBase[i]!
      (bfsTableK (vStepK i) (vGens[i]!).length vBase[i]! 5000) := kinv_bfsTableK _ _
  have e : vecTab i = (bfsTableK (vStepK i) (vGens[i]!).length vBase[i]! 5000).1 :=
    bfsTable_eq_K hstep _ _
  rw [e]
  refine ⟨⟨⟨fun g hg' => ⟨?_, (hg g hg').2⟩, derivOK_of_KInv hstep I⟩,
    tabNodupLt_of_KInv I hx0 hB⟩, ?_⟩
  · rw [inAutOK_eq_K]
    exact (hg g hg').1.2
  · rw [← (bfsQ_eq (step := vStepK i) (ngen := (vGens[i]!).length) vBase[i]! 5000).1]
    exact hs

end CFSG.KS.ASVolI

end
