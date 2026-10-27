module

public import Certificates.Data.Kernel.HMathieu.Orb
public import CFSG.Quasithin.Background.HLU24Inputs

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Parab CFSG.Quasithin.H.LU24

theorem KT.mem_ins (t : KT) (k x : Nat) : (t.ins k).mem x = (x == k || t.mem x) := by
  induction t with
  | leaf =>
    simp only [KT.ins, KT.mem]
    by_cases hx : x = k <;> simp [hx]
  | node l k0 r ihl ihr =>
    unfold KT.ins
    by_cases h0 : k = k0
    · subst h0
      rw [if_pos rfl]
      unfold KT.mem
      by_cases hx : x = k <;> simp [hx]
    · by_cases hk : k < k0
      · rw [if_neg h0, if_pos hk]
        unfold KT.mem
        rw [ihl]
        by_cases hx : x = k0
        · simp [hx]
        · by_cases hxl : x < k0
          · simp [hx, hxl]
          · have : x ≠ k := by omega
            simp [hx, hxl, this]
      · rw [if_neg h0, if_neg hk]
        unfold KT.mem
        rw [ihr]
        by_cases hx : x = k0
        · simp [hx, Ne.symm h0]
        · by_cases hxl : x < k0
          · have : x ≠ k := by omega
            simp [hx, hxl, this]
          · simp [hx, hxl]

theorem orbBases_append (cs : List (List Nat)) (d : List Nat) :
    ∀ (st : List (Nat × Nat)) (bs : List (List Nat)) (g i : Nat),
      orbBases cs d bs (st ++ [(g, i)]) =
        orbBases cs d bs st ++ [((orbBases cs d bs st).getD i d).map (actM (cs.getD g []))]
  | [], bs, g, i => rfl
  | (g', i') :: st, bs, g, i => by
    rw [List.cons_append, orbBases, orbBases, orbBases_append cs d st]

structure OInv (n : Nat) (cs : List (List Nat)) (d : List Nat)
    (s : Array (List Nat) × Std.HashSet Nat × Array (Nat × Nat)) : Prop where
  bases : s.1.toList = orbBases cs d [d] s.2.2.toList
  steps : ∀ e ∈ s.2.2.toList, e.1 < cs.length
  seen : ∀ k, s.2.1.contains k = true ↔ k ∈ s.1.toList.map maskKey
  nodup : (s.1.toList.map maskKey).Nodup
  lt : ∀ b ∈ s.1.toList, ∀ x ∈ b, x < 2 ^ n
  size : s.2.2.size + 1 = s.1.size

structure ORel (s : Array (List Nat) × Std.HashSet Nat × Array (Nat × Nat)) (i : Nat)
    (t : OT) : Prop where
  queue : s.1.toList.drop i = t.front ++ t.back.reverse
  cnt : t.cnt = s.1.size
  tree : ∀ k, t.tree.mem k = s.2.1.contains k

variable {n : Nat} {cs : List (List Nat)} {d : List Nat}

theorem getD_toList {s : Array (List Nat)} {i : Nat} (hi : i < s.size) (e : List Nat) :
    s.toList.getD i e = s.getD i [] := by
  simp [List.getD_eq_getElem?_getD, Array.getD, hi]

theorem round_step (hcs : ∀ c ∈ cs, ∀ x ∈ c, x < 2 ^ n)
    {s : Array (List Nat) × Std.HashSet Nat × Array (Nat × Nat)} {i : Nat} {t : OT}
    (hi : i < s.1.size) (I : OInv n cs d s) (R : ORel s (i + 1) t) {g : Nat}
    (hg : g < cs.length) :
    OInv n cs d (orbRound cs i s g) ∧ ORel (orbRound cs i s g) (i + 1)
      (otRound cs (s.1.getD i []) t g) ∧ (orbRound cs i s g).1.getD i [] = s.1.getD i [] := by
  obtain ⟨bs, seen, st⟩ := s
  simp only at hi I R ⊢
  set b := bs.getD i [] with hb
  set nb := b.map (actM (cs.getD g [])) with hnb
  have hmem : t.tree.mem (maskKey nb) = seen.contains (maskKey nb) := R.tree _
  unfold orbRound otRound
  simp only
  rw [← hb, ← hnb, hmem]
  cases hc : seen.contains (maskKey nb)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hk : maskKey nb ∉ bs.toList.map maskKey := fun h => by
      rw [← I.seen] at h
      rw [hc] at h
      exact Bool.false_ne_true h
    have hbi : (orbBases cs d [d] st.toList).getD i d = b := by
      rw [← I.bases, getD_toList hi]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [Array.toList_push, Array.toList_push, orbBases_append, ← I.bases]
      simp only
      rw [getD_toList hi d]
    · intro e he
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact I.steps e he
      · exact hg
    · intro k
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, I.seen, Array.toList_push,
        List.map_append, List.mem_append, List.map_singleton, List.mem_singleton]
      simp only
      exact Or.comm.trans (or_congr_right eq_comm)
    · rw [Array.toList_push, List.map_append, List.map_singleton]
      exact List.nodup_append.2 ⟨I.nodup, List.nodup_singleton _, fun a ha c hc' e =>
        hk (by rw [List.mem_singleton] at hc'; rw [e, hc'] at ha; exact ha)⟩
    · intro c hc' x hx
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hc'
      rcases hc' with hc' | rfl
      · exact I.lt c hc' x hx
      · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
        refine actM_lt (fun c' hc'' => hcs _ ?_ c' hc'') _
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg]
        exact List.getElem_mem hg
    · rw [Array.size_push, Array.size_push, I.size]
    · rw [Array.toList_push, List.drop_append_of_le_length (by simp; omega), R.queue,
        List.reverse_cons, List.append_assoc]
    · rw [Array.size_push, R.cnt]
    · intro k
      rw [KT.mem_ins, Std.HashSet.contains_insert, R.tree, Bool.beq_comm]
    · rw [hb, ← getD_toList (by rw [Array.size_push]; omega) [], ← getD_toList hi [],
        Array.toList_push, List.getD_append _ _ _ _ (by simpa using hi)]
  · simp only [↓reduceIte]
    exact ⟨I, R, rfl⟩

theorem round_all (hcs : ∀ c ∈ cs, ∀ x ∈ c, x < 2 ^ n) {i : Nat} :
    ∀ (L : List Nat), (∀ g ∈ L, g < cs.length) →
      ∀ (s : Array (List Nat) × Std.HashSet Nat × Array (Nat × Nat)) (t : OT),
      i < s.1.size → OInv n cs d s → ORel s (i + 1) t →
      OInv n cs d (L.foldl (orbRound cs i) s) ∧
        ORel (L.foldl (orbRound cs i) s) (i + 1) (L.foldl (otRound cs (s.1.getD i [])) t) ∧
        (L.foldl (orbRound cs i) s).1.getD i [] = s.1.getD i [] ∧
        i < (L.foldl (orbRound cs i) s).1.size := by
  intro L
  induction L with
  | nil => intro _ s t hi I R; exact ⟨I, R, rfl, hi⟩
  | cons g L ih =>
    intro hL s t hi I R
    obtain ⟨I', R', e⟩ := round_step hcs hi I R (hL g List.mem_cons_self)
    have hle : s.1.size ≤ (orbRound cs i s g).1.size := by
      obtain ⟨bs, seen, st⟩ := s
      unfold orbRound
      simp only
      by_cases h : seen.contains (maskKey ((bs.getD i []).map (actM (cs.getD g [])))) = true
      · rw [if_pos h]
      · rw [if_neg h, Array.size_push]
        omega
    have hi' : i < (orbRound cs i s g).1.size := by omega
    obtain ⟨A, B, C, D⟩ := ih (fun g' hg' => hL g' (List.mem_cons_of_mem g hg')) _ _ hi' I' R'
    rw [List.foldl_cons, List.foldl_cons]
    rw [e] at B C
    exact ⟨A, B, C, D⟩

theorem getD_eq_of_drop {s : Array (List Nat)} {i : Nat} {b : List Nat} {rest : List (List Nat)}
    (h : s.toList.drop i = b :: rest) : s.getD i [] = b ∧ i < s.size := by
  have hi : i < s.size := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by simp; omega)] at h
    cases h
  refine ⟨?_, hi⟩
  rw [← getD_toList hi [], List.getD_eq_getElem?_getD]
  have := congrArg List.head? h
  rw [List.head?_drop] at this
  simp [this]

theorem orbTwin_eq (hcs : ∀ c ∈ cs, ∀ x ∈ c, x < 2 ^ n) :
    ∀ (f i : Nat) (s : Array (List Nat) × Std.HashSet Nat × Array (Nat × Nat)) (t : OT),
      OInv n cs d s → ORel s i t → i ≤ s.1.size →
      ∃ s', OInv n cs d s' ∧ orbBFS cs f i s = s'.2.2 ∧ orbTwin cs f t = s'.1.size := by
  intro f
  induction f with
  | zero => intro i s t I R _; exact ⟨s, I, rfl, R.cnt⟩
  | succ f ih =>
    intro i s t I R hi
    have hrange : ∀ g ∈ List.range cs.length, g < cs.length := fun g hg => List.mem_range.1 hg
    rcases Nat.lt_or_ge i s.1.size with hlt | hge
    · obtain ⟨fr, bk, c, tr⟩ := t
      have hq := R.queue
      simp only at hq
      have hstep : ∀ (b : List Nat) (fr' bk' : List (List Nat)),
          s.1.toList.drop i = b :: (fr' ++ bk'.reverse) →
          orbTwin cs f ((List.range cs.length).foldl (otRound cs b) ⟨fr', bk', c, tr⟩) =
            orbTwin cs (f + 1) ⟨fr, bk, c, tr⟩ →
          ∃ s', OInv n cs d s' ∧ orbBFS cs (f + 1) i s = s'.2.2 ∧
            orbTwin cs (f + 1) ⟨fr, bk, c, tr⟩ = s'.1.size := by
        intro b fr' bk' hd he
        obtain ⟨hb, -⟩ := getD_eq_of_drop hd
        have R1 : ORel s (i + 1) ⟨fr', bk', c, tr⟩ := ⟨by
            rw [← List.drop_drop, hd]
            rfl, R.cnt, R.tree⟩
        obtain ⟨A, B, C, D⟩ := round_all hcs (List.range cs.length) hrange s _ hlt I R1
        rw [hb] at B
        obtain ⟨s', I', e1, e2⟩ := ih (i + 1) _ _ A B (by omega)
        refine ⟨s', I', ?_, ?_⟩
        · rw [orbBFS, if_pos hlt]
          exact e1
        · rw [← he]
          exact e2
      cases fr with
      | cons b fr' =>
        exact hstep b fr' bk (by rw [hq]; rfl) rfl
      | nil =>
        cases hbk : bk.reverse with
        | nil =>
          rw [hbk] at hq
          simp at hq
          omega
        | cons b fr' =>
          rw [hbk] at hq
          refine hstep b fr' [] (by rw [hq]; simp) ?_
          simp only [orbTwin, hbk]
    · have hiq : s.1.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
      refine ⟨s, I, ?_, ?_⟩
      · rw [orbBFS, if_neg (by omega)]
      · obtain ⟨fr, bk, c, tr⟩ := t
        have hq := R.queue
        rw [hiq] at hq
        simp only at hq
        have hfr : fr = [] := by
          cases fr with
          | nil => rfl
          | cons _ _ => simp at hq
        have hbk : bk.reverse = [] := by
          rw [hfr, List.nil_append] at hq
          exact hq.symm
        subst hfr
        simp only [orbTwin, hbk]
        exact R.cnt

theorem orbCheck_of (hcs : ∀ c ∈ cs, ∀ x ∈ c, x < 2 ^ n) (hd : ∀ x ∈ d, x < 2 ^ n) {N : Nat}
    (h : orbCount cs d N = N) : orbCheck n cs d N = true := by
  have I0 : OInv n cs d (#[d], (∅ : Std.HashSet Nat).insert (maskKey d), #[]) := by
    refine ⟨rfl, by simp, fun k => ?_, by simp, ?_, rfl⟩
    · rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false, beq_iff_eq]
      change _ ↔ k ∈ [maskKey d]
      rw [List.mem_singleton]
      exact eq_comm
    · intro b hb x hx
      simp only [List.mem_singleton] at hb
      subst hb
      exact hd x hx
  have R0 : ORel (#[d], (∅ : Std.HashSet Nat).insert (maskKey d), #[]) 0
      ⟨[d], [], 1, KT.leaf.ins (maskKey d)⟩ := by
    refine ⟨rfl, rfl, fun k => ?_⟩
    rw [KT.mem_ins, Std.HashSet.contains_insert]
    simp [KT.mem, Bool.beq_comm]
  obtain ⟨s', I', e1, e2⟩ := orbTwin_eq hcs (N + 1) 0 _ _ I0 R0 (Nat.zero_le _)
  unfold orbCount at h
  rw [e2] at h
  have hst : orbSteps cs d N = s'.2.2.toList := by
    unfold orbSteps
    rw [e1]
  unfold orbCheck
  simp only
  rw [hst, ← I'.bases, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true,
    List.all_eq_true, decide_eq_true_iff, beq_iff_eq]
  refine ⟨⟨⟨fun e he => decide_eq_true (I'.steps e he), fun b hb => ?_⟩, I'.nodup⟩,
    by rw [Array.length_toList, h]⟩
  rw [List.all_eq_true]
  exact fun x hx => decide_eq_true (I'.lt b hb x hx)

end CFSG.KC.HMathieu

end
