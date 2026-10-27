module

public import Certificates.Data.Kernel.Spor.Fi24ThreeAK
public import CFSG.Certificates.Kernel.Spor.Fi24NetPtSound

public section

namespace CFSG.KS.Fi24Kit

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.Fi24Net
  CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeAK CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt
  CFSG.KC.KDense.SortAux

@[expose] noncomputable def wN (NW : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  w.foldr (fun l y => LN NW l y) x

@[expose] def WV (NW : Nat → Nat → Nat) (w : List Nat) : Prop := ∀ l ∈ w, NV (NW (l / 2))

theorem WV.tail {NW : Nat → Nat → Nat} {l : Nat} {w : List Nat} (h : WV NW (l :: w)) : WV NW w :=
  fun l' hl' => h l' (List.mem_cons_of_mem l hl')

theorem wN_append (NW : Nat → Nat → Nat) (u v : List Nat) (x : Nat) :
    wN NW (u ++ v) x = wN NW u (wN NW v x) := by
  unfold wN
  rw [List.foldr_append]

theorem wP_eq (NW : Nat → Nat → Nat) : ∀ (w : List Nat) (x : Nat), wP NW w x = wN NW w x
  | [], _ => rfl
  | l :: w, x => by
    have e : wP NW (l :: w) x = letN NW l (wP NW w x) := Fi24NetPt.strictN_eq _ _
    rw [e, wP_eq NW w x, letN_eq]
    rfl

theorem LN_lt {NW : Nat → Nat → Nat} {l : Nat} (h : NV (NW (l / 2))) {q : Nat} (hq : q < 524288) :
    LN NW l q < 524288 := by
  unfold LN
  by_cases hl : l % 2 = 0
  · rw [if_pos hl]
    exact pF_lt h hq
  · rw [if_neg hl]
    exact pR_lt h hq

theorem wN_lt {NW : Nat → Nat → Nat} : ∀ (w : List Nat), WV NW w → ∀ q < 524288, wN NW w q < 524288
  | [], _, _, hq => hq
  | l :: w, h, q, hq => LN_lt (h l List.mem_cons_self) (wN_lt w h.tail q hq)

theorem testBit_walkP {NW : Nat → Nat → Nat} : ∀ (w : List Nat), WV NW w →
    ∀ v q, (walkP NW w v).testBit q = v.testBit (wN NW w q)
  | [], _, _, _ => rfl
  | l :: w, h, v, q => by
    have e : walkP NW (l :: w) v = walkP NW w (planeL NW l v) := Fi24NetPt.strictN_eq _ _
    rw [e, testBit_walkP w h.tail (planeL NW l v) q, testBit_planeL (h l List.mem_cons_self)]
    rfl

theorem tp_spec {NW : Nat → Nat → Nat} {NT : Nat → Nat} {wA wB : List Nat} (hT : NV NT)
    (h0 : NV (NW 0)) (h1 : NV (NW 1)) (hA : WV NW wA) (hB : WV NW wB)
    (h : ∀ k < 19, tpOK NW NT wA wB k = true) :
    ∀ x < 524288, pF NT (pF (NW 0) x) = wN NW wA (pF NT x) ∧
      pF NT (pF (NW 1) x) = wN NW wB (pF NT x) := by
  have key : ∀ k < 19, ∀ x < 524288,
      (tpl k).testBit (pF NT (pF (NW 0) x)) = (tpl k).testBit (wN NW wA (pF NT x)) ∧
      (tpl k).testBit (pF NT (pF (NW 1) x)) = (tpl k).testBit (wN NW wB (pF NT x)) := by
    intro k hk x _
    have e : andB (Nat.beq (netF (NW 0) (netF NT (tpl k))) (netF NT (walkP NW wA (tpl k))))
        (Nat.beq (netF (NW 1) (netF NT (tpl k))) (netF NT (walkP NW wB (tpl k)))) = true := by
      have e0 := h k hk
      unfold tpOK at e0
      rw [letB_eq', letB_eq'] at e0
      exact e0
    obtain ⟨e1, e2⟩ := andB_true e
    have f1 : (netF (NW 0) (netF NT (tpl k))).testBit x = (netF NT (walkP NW wA (tpl k))).testBit x := by
      rw [Nat.eq_of_beq_eq_true e1]
    have f2 : (netF (NW 1) (netF NT (tpl k))).testBit x = (netF NT (walkP NW wB (tpl k))).testBit x := by
      rw [Nat.eq_of_beq_eq_true e2]
    rw [testBit_netF h0, testBit_netF hT, testBit_netF hT, testBit_walkP wA hA] at f1
    rw [testBit_netF h1, testBit_netF hT, testBit_netF hT, testBit_walkP wB hB] at f2
    exact ⟨f1, f2⟩
  intro x hx
  refine ⟨perm_of_tpl (f := fun x => pF NT (pF (NW 0) x)) (g := fun x => wN NW wA (pF NT x))
      (fun q hq => pF_lt hT (pF_lt h0 hq)) (fun q hq => wN_lt wA hA _ (pF_lt hT hq))
      (fun k hk q hq => (key k hk q hq).1) x hx,
    perm_of_tpl (f := fun x => pF NT (pF (NW 1) x)) (g := fun x => wN NW wB (pF NT x))
      (fun q hq => pF_lt hT (pF_lt h1 hq)) (fun q hq => wN_lt wB hB _ (pF_lt hT hq))
      (fun k hk q hq => (key k hk q hq).2) x hx⟩

theorem testBit_stepS {NW : Nat → Nat → Nat} (S x : Nat) : ∀ {ls : List Nat}, WV NW ls →
    (stepS NW ls S).testBit x = true → S.testBit x = true ∨ ∃ l ∈ ls, S.testBit (LN NW l x) = true
  | [], _, h => Or.inl h
  | l :: ls, hl, h => by
    have e : (stepS NW (l :: ls) S).testBit x = (planeL NW l S ||| stepS NW ls S).testBit x := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [testBit_planeL (hl l List.mem_cons_self)] at h
      exact Or.inr ⟨l, List.mem_cons_self, h⟩
    · rcases testBit_stepS S x hl.tail h with h' | ⟨l', hl', h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨l', List.mem_cons_of_mem l hl', h'⟩

theorem iterS_spec {NW : Nat → Nat → Nat} {ls : List Nat} (hl : WV NW ls) (S : Nat) :
    ∀ d x, (iterS NW ls d S).testBit x = true →
      ∃ w : List Nat, (∀ l ∈ w, l ∈ ls) ∧ S.testBit (wN NW w x) = true
  | 0, _, h => ⟨[], fun _ hl => absurd hl List.not_mem_nil, h⟩
  | d + 1, x, h => by
    have e : iterS NW ls (d + 1) S = stepS NW ls (iterS NW ls d S) := Fi24NetPt.strictN_eq _ _
    rw [e] at h
    rcases testBit_stepS _ x hl h with h1 | ⟨l, hl', h1⟩
    · exact iterS_spec hl S d x h1
    · obtain ⟨w, hw, hS⟩ := iterS_spec hl S d _ h1
      refine ⟨w ++ [l], fun l' h' => ?_, ?_⟩
      · rcases List.mem_append.1 h' with h' | h'
        · exact hw l' h'
        · rw [List.mem_singleton.1 h']
          exact hl'
      · rw [wN_append]
        exact hS

theorem ptsM_testBit {x : Nat} (hx : x < 306936) : ptsM.testBit x = true := by
  unfold ptsM
  rw [testBit_ones]
  exact decide_eq_true hx

theorem cover_spec {NW : Nat → Nat → Nat} {ls : List Nat} {d S F : Nat} (hl : WV NW ls)
    (h : coverOK NW ls d S F = true) {x : Nat} (hx : x < 306936) :
    F.testBit x = true ∨ ∃ w : List Nat, (∀ l ∈ w, l ∈ ls) ∧ S.testBit (wN NW w x) = true := by
  unfold coverOK at h
  have e : ((iterS NW ls d S ||| F) &&& ptsM).testBit x = ptsM.testBit x := by
    have e0 := Nat.eq_of_beq_eq_true h
    change (iterS NW ls d S ||| F) &&& ptsM = ptsM at e0
    rw [e0]
  rw [Nat.testBit_and, Nat.testBit_or, ptsM_testBit hx, Bool.and_true, Bool.or_eq_true] at e
  rcases e with e | e
  · exact Or.inr (iterS_spec hl S d x e)
  · exact Or.inl e

theorem allL_spec {α : Type} {f : α → Bool} : ∀ {l : List α}, allL f l = true → ∀ a ∈ l, f a = true
  | [], _, _, ha => absurd ha List.not_mem_nil
  | a :: l, h, b, hb => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h1
    · exact allL_spec h2 b hb

theorem beq_true {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem fail_spec {OL NT : Nat → Nat} {r q : Nat} (h : failOK OL NT r q = true) :
    clsK OL NT r (sK OL NT (clsK OL NT r q)) ≠ sKi OL NT q := by
  intro e
  have e' : failOK OL NT r q = notB (Nat.beq (clsK OL NT r (sK OL NT (clsK OL NT r q)))
      (sKi OL NT q)) := by
    unfold failOK
    rw [Fi24NetPt.strictN_eq, Fi24NetPt.strictN_eq]
  rw [e', e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem d4_spec {NW : Nat → Nat → Nat} {W : Nat → List Nat} {R : List (List (Nat × Bool))} {x : Nat}
    (h : d4At NW W R x = true) :
    (∀ i ∈ [0, 1, 2, 3, 4, 5, 6, 7], wN NW (cube (W i)) x = x) ∧
    (∀ e ∈ [(0, 1), (1, 2), (1, 3)], (∀ w ∈ sixW W e.1 e.2, wN NW (cube w) x = x) ∧
      ∀ r ∈ R, wN NW (relW (sixW W e.1 e.2) r) x = x) ∧
    (∀ e ∈ [(0, 2), (0, 3), (2, 3)], ∀ u ∈ [0, 1], ∀ v ∈ [0, 1],
      wN NW (W (2 * e.1 + u) ++ W (2 * e.2 + v)) x = wN NW (W (2 * e.2 + v) ++ W (2 * e.1 + u)) x) := by
  unfold d4At at h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h⟩ := andB_true h
  obtain ⟨h4, h⟩ := andB_true h
  obtain ⟨h5, h⟩ := andB_true h
  obtain ⟨h6, h7⟩ := andB_true h
  have edge : ∀ {i j : Nat}, edgeAt NW W R i j x = true →
      (∀ w ∈ sixW W i j, wN NW (cube w) x = x) ∧
        ∀ r ∈ R, wN NW (relW (sixW W i j) r) x = x := by
    intro i j he
    unfold edgeAt at he
    obtain ⟨a, b⟩ := andB_true he
    exact ⟨fun w hw => by rw [← wP_eq]; exact beq_true (allL_spec a w hw),
      fun r hr => by rw [← wP_eq]; exact beq_true (allL_spec b r hr)⟩
  have comm : ∀ {a b : Nat}, commAt NW W a b x = true → ∀ u ∈ [0, 1], ∀ v ∈ [0, 1],
      wN NW (W (2 * a + u) ++ W (2 * b + v)) x = wN NW (W (2 * b + v) ++ W (2 * a + u)) x := by
    intro a b hc u hu v hv
    unfold commAt at hc
    rw [← wP_eq, ← wP_eq]
    exact beq_true (allL_spec (allL_spec hc u hu) v hv)
  refine ⟨fun i hi => by rw [← wP_eq]; exact beq_true (allL_spec h1 i hi), ?_, ?_⟩
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    exacts [edge h2, edge h3, edge h4]
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    exacts [comm h5, comm h6, comm h7]

theorem conj_spec {NW : Nat → Nat → Nat} {OL NT : Nat → Nat} {c : List Nat} {x : Nat}
    (h : conjOK NW OL NT c x = true) : wN NW (c ++ [18]) x = sK OL NT (wN NW c x) := by
  unfold conjOK at h
  rw [Fi24NetPt.strictN_eq, wP_eq, wP_eq] at h
  exact beq_true h

end CFSG.KS.Fi24Kit

end
