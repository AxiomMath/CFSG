module

public import CFSG.Certificates.Kernel.TwoNodeSmall.PtsK
public import CFSG.Certificates.Kernel.TwoNodeSmall.WitKOK
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallClosed

public section

namespace CFSG.TwoNodeSmall.WitK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.PtsK

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem chkPt_verifyK (P : Pt) (r : Rec) (h : chkPt P r = true) :
    (r.1 = 0 → ∃ w, verify P (.kernel w) = true) ∧ (r.1 = 1 → ∃ t, verify P (.transv t) = true) ∧
    (r.1 = 2 → ∃ o, verify P (.order o) = true) ∧ (r.1 = 3 → ∃ c, verify P (.weyl c) = true) := by
  obtain ⟨k, sm, clo, lv, ex⟩ := r
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_⟩ <;> change k = _ at hk <;> subst hk
  · change (Nat.beq P.p 3 && Nat.ble 1 P.D && Nat.ble P.D 10 &&
      kK (Nat.mul 3 (ones P.D)) (Nat.mul 16 (Nat.sub P.D 1)) P.nFrame (gensK P) (pk P.D P.x)
        (pk P.D sm)) = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
    obtain ⟨⟨⟨hp, -⟩, hD⟩, hk⟩ := h
    exact ⟨sm, OK.kK_verify hp hD hk⟩
  · obtain ⟨hp, hD, -, hfact, hWF, hwf, Dl, hs, -, -, hk⟩ := OK.chk_common (by norm_num) h
    obtain ⟨t, ht⟩ := OK.tK_verify hp hD hWF hs hk
    refine ⟨t, ?_⟩
    change (wfCheck P && verifyT P t) = true
    rw [hwf, ht]
    rfl
  · exact OK.order_verify h
  · exact OK.weyl_verify h

theorem chkPt_kind {P : Pt} {r : Rec} (h : chkPt P r = true) : r.1 ≤ 3 := by
  obtain ⟨k, rest⟩ := r
  change k ≤ 3
  by_contra hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
  have e0 : Nat.beq (m + 4) 0 = false := rfl
  have e1 : Nat.beq (m + 4) 1 = false := rfl
  have e2 : Nat.beq (m + 4) 2 = false := rfl
  have e3 : Nat.beq (m + 4) 3 = false := rfl
  unfold chkPt at h
  simp only [e0, e1, e2, e3, cond_false, Bool.and_false] at h
  exact Bool.false_ne_true h

theorem chkPt_verify (P : Pt) (r : Rec) (h : chkPt P r = true) : ∃ w, verify P w = true := by
  obtain ⟨h0, h1, h2, h3⟩ := chkPt_verifyK P r h
  have hk := chkPt_kind h
  rcases Nat.lt_or_ge r.1 2 with hk2 | hk2
  · rcases Nat.lt_or_ge r.1 1 with hk1 | hk1
    · obtain ⟨w, hw⟩ := h0 (by omega)
      exact ⟨_, hw⟩
    · obtain ⟨w, hw⟩ := h1 (by omega)
      exact ⟨_, hw⟩
  · rcases Nat.lt_or_ge r.1 3 with hk3 | hk3
    · obtain ⟨w, hw⟩ := h2 (by omega)
      exact ⟨_, hw⟩
    · obtain ⟨w, hw⟩ := h3 (by omega)
      exact ⟨_, hw⟩

theorem chkPt_closed {P : Pt}
    [Fact P.p.Prime] {r : Rec} (h : chkPt P r = true) : P.Closed := by
  obtain ⟨w, hw⟩ := chkPt_verify P r h
  exact verify_closed hw

theorem dropK_eq {α : Type} (k : Nat) (l : List α) : dropK k l = l.drop k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (dropK k l).tail = _
    rw [ih, List.tail_drop]

theorem all2_spec {α β : Type} (f : α → β → Bool) : ∀ (l1 : List α) (l2 : List β),
    all2 f l1 l2 = true → l1.length = l2.length ∧
      ∀ k (h1 : k < l1.length) (h2 : k < l2.length), f l1[k] l2[k] = true
  | [], l2, h => by
    have e : all2 f [] l2 = l2.isEmpty := rfl
    rw [e, List.isEmpty_iff] at h
    subst h
    exact ⟨rfl, fun k h1 => absurd h1 (Nat.not_lt_zero _)⟩
  | x :: xs, [], h => by
    have e : all2 f (x :: xs) [] = false := rfl
    rw [e] at h
    exact absurd h Bool.false_ne_true
  | x :: xs, y :: ys, h => by
    have e : all2 f (x :: xs) (y :: ys) = (f x y && all2 f xs ys) := rfl
    rw [e, Bool.and_eq_true] at h
    obtain ⟨hl, hk⟩ := all2_spec f xs ys h.2
    refine ⟨by simp [hl], fun k h1 h2 => ?_⟩
    cases k with
    | zero => simpa using h.1
    | succ k => simpa using hk k (by simpa using h1) (by simpa using h2)

theorem chunk_mem {B S : Nat} (hS : 0 < S) {pts : List Pt} {ws : List Rec}
    (h : ∀ s < S, chunkK B S pts ws s = true) : ∀ P ∈ pts, ∃ r, chkPt P r = true := by
  have hlen : pts.length = ws.length ∧ ws.length ≤ B * S := by
    have h0 := h 0 hS
    simp only [chunkK, Nat.beq_refl, cond_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h0
    exact ⟨h0.1.1, h0.1.2⟩
  intro P hP
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hP
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with hB | hB
    · rw [hB, Nat.zero_mul] at hlen; omega
    · exact hB
  have hs : i / B < S := (Nat.div_lt_iff_lt_mul hB).2 (by rw [Nat.mul_comm]; omega)
  have hc := h (i / B) hs
  simp only [chunkK, dropK_eq, Bool.and_eq_true, Nat.mul_eq] at hc
  obtain ⟨-, hk⟩ := all2_spec chkPt _ _ hc.2
  have e := Nat.div_add_mod' i B
  have hm := Nat.mod_lt i hB
  generalize i / B * B = a at hk e
  have hk' := hk (i % B) (by simp only [List.length_take, List.length_drop]; omega)
    (by simp only [List.length_take, List.length_drop]; omega)
  simp only [List.getElem_take, List.getElem_drop, e] at hk'
  exact ⟨_, hk'⟩

theorem optK_eq {e m : Nat} (hm : m < (kopts ()).length) :
    optK (10 * e + m) = (kopts ())[m] := by
  have h : (10 * e + m) % 10 = m := by
    have : (kopts ()).length = 10 := rfl
    omega
  simp only [optK, h, List.getD_eq_getElem _ _ hm]

theorem grp {e m : Nat} (he : e ∈ [0, 1, 2]) (hm : m < (kopts ()).length) :
    10 * e + m < 30 ∧ (10 * e + m) / 10 = e := by
  have : (kopts ()).length = 10 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  omega

theorem mem_pts8 {P : Pt} (hP : P ∈ pts8 ()) : ∃ g < 30, P ∈ blk8 g := by
  rw [pts8_eq] at hP
  simp only [pts8K, List.mem_flatMap] at hP
  obtain ⟨e, he, o, ho, hP⟩ := hP
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem ho
  obtain ⟨h1, h2⟩ := grp he hm
  refine ⟨10 * e + m, h1, ?_⟩
  simp only [blk8, h2, optK_eq hm]
  exact hP

theorem mem_pts9m {P : Pt} (hP : P ∈ pts9m ()) : ∃ g < 30, P ∈ blk9m g := by
  rw [pts9m_eq] at hP
  simp only [pts9mK, List.mem_flatMap] at hP
  obtain ⟨e, he, o, ho, hP⟩ := hP
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem ho
  obtain ⟨h1, h2⟩ := grp he hm
  refine ⟨10 * e + m, h1, ?_⟩
  simp only [blk9m, h2, optK_eq hm]
  exact hP

theorem mem_pts9 {P : Pt} (hP : P ∈ pts9 ()) : ∃ g < 30, P ∈ blk9 g := by
  rw [pts9_eq] at hP
  simp only [pts9K, List.mem_flatMap] at hP
  obtain ⟨e, he, o, ho, hP⟩ := hP
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem ho
  obtain ⟨h1, h2⟩ := grp he hm
  refine ⟨10 * e + m, h1, ?_⟩
  simp only [blk9, h2, optK_eq hm]
  simp only [List.mem_flatMap] at hP ⊢
  exact hP

theorem closed_of_chunks
    {w8 w9 w9m : List (List Rec)}
    (h8 : ∀ g < 30, ∀ s < 3, chunkK 6 3 (blk8 g) (w8.getD g []) s = true)
    (h9 : ∀ g < 30, ∀ s < 3, chunkK 18 3 (blk9 g) (w9.getD g []) s = true)
    (h9m : ∀ g < 30, ∀ s < 3, chunkK 6 3 (blk9m g) (w9m.getD g []) s = true) :
    ∀ P ∈ pts8 () ++ pts9 () ++ pts9m (), ∀ [Fact P.p.Prime], P.Closed := by
  intro P hP _
  simp only [List.mem_append] at hP
  rcases hP with (hP | hP) | hP
  · obtain ⟨g, hg, hP⟩ := mem_pts8 hP
    obtain ⟨r, hr⟩ := chunk_mem (by decide) (h8 g hg) P hP
    exact chkPt_closed hr
  · obtain ⟨g, hg, hP⟩ := mem_pts9 hP
    obtain ⟨r, hr⟩ := chunk_mem (by decide) (h9 g hg) P hP
    exact chkPt_closed hr
  · obtain ⟨g, hg, hP⟩ := mem_pts9m hP
    obtain ⟨r, hr⟩ := chunk_mem (by decide) (h9m g hg) P hP
    exact chkPt_closed hr

theorem groups_of_90 {c : Nat → Prop} (h : ∀ k < 90, c k) : ∀ g < 30, ∀ s < 3, c (3 * g + s) :=
  fun g hg s hs => h _ (by omega)

end CFSG.TwoNodeSmall.WitK

end
