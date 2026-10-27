module

public import CFSG.Certificates.Kernel.M24L2.BfsSound

public section

namespace CFSG.KC.M24L2

variable {α : Type}

@[expose] def queueOf (t : BS α) : List (Nat × List α) := t.front ++ t.back.reverse

@[expose] def Closed (keyN : Nat → Nat) (lc : α → Nat) (lets : List α) (L : List (Nat × List α))
    (e : Nat × List α) : Prop :=
  ∀ l ∈ lets, ∃ e' ∈ L, keyN e'.1 = keyN (mulC e.1 (lc l))

structure TI (N : Nat) (keyN : Nat → Nat) (lc : α → Nat) (lets : List α) (c0 : Nat) (r : Nat)
    (t : BS α) : Prop where
  split : ∃ P, t.all.reverse = P ++ queueOf t ∧ (P.length = r ∨ queueOf t = []) ∧
    ∀ e ∈ P, Closed keyN lc lets t.all e
  nd : (t.all.map fun e => keyN e.1).Nodup
  bd : ∀ e ∈ t.all, keyN e.1 < N
  mb : ∀ k, t.mask.testBit (k + 64) = t.all.any fun e => keyN e.1 == k
  root : (c0, []) ∈ t.all

theorem Closed.mono {keyN : Nat → Nat} {lc : α → Nat} {lets : List α} {L L' : List (Nat × List α)}
    {e : Nat × List α} (h : Closed keyN lc lets L e) (hL : ∀ x ∈ L, x ∈ L') :
    Closed keyN lc lets L' e := fun l hl => by
  obtain ⟨e', he', hk⟩ := h l hl
  exact ⟨e', hL e' he', hk⟩

section Inv

variable {N : Nat} {keyN : Nat → Nat} {lc : α → Nat} {lets : List α} {c0 : Nat}

structure TJ (N : Nat) (keyN : Nat → Nat) (lc : α → Nat) (lets : List α) (c0 : Nat)
    (P : List (Nat × List α)) (e : Nat × List α) (D : List α) (t : BS α) : Prop where
  split : t.all.reverse = P ++ e :: queueOf t
  cl : ∀ x ∈ P, Closed keyN lc lets t.all x
  done : ∀ l ∈ D, ∃ e' ∈ t.all, keyN e'.1 = keyN (mulC e.1 (lc l))
  nd : (t.all.map fun e => keyN e.1).Nodup
  bd : ∀ e ∈ t.all, keyN e.1 < N
  mb : ∀ k, t.mask.testBit (k + 64) = t.all.any fun e => keyN e.1 == k
  root : (c0, []) ∈ t.all

theorem tj_inner (hN : ∀ c < 2 ^ 20, keyN c < N) {P : List (Nat × List α)} {e : Nat × List α}
    {D : List α} {t : BS α} (h : TJ N keyN lc lets c0 P e D t) (l : α) :
    TJ N keyN lc lets c0 P e (D ++ [l]) (innerK keyN lc e.1 e.2 t l) := by
  unfold innerK
  simp only [letN_eq, land_pow_beq]
  have hy := mulC_lt e.1 (lc l)
  generalize hyv : mulC e.1 (lc l) = y at hy ⊢
  rcases hb : t.mask.testBit (Nat.add (keyN y) 64) with _ | _
  · simp only [Bool.not_false]
    change t.mask.testBit (keyN y + 64) = false at hb
    have hany : (t.all.any fun x => keyN x.1 == keyN y) = false := by rw [← h.mb]; exact hb
    have hsub : ∀ x ∈ t.all, x ∈ (y, e.2 ++ [l]) :: t.all := fun x hx => List.mem_cons_of_mem _ hx
    change TJ N keyN lc lets c0 P e (D ++ [l])
      (BS.mk t.front ((y, e.2 ++ [l]) :: t.back) ((y, e.2 ++ [l]) :: t.all) (addKey t.mask (keyN y)))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.reverse_cons, h.split, queueOf, List.append_assoc, List.cons_append]
    · exact fun x hx => (h.cl x hx).mono hsub
    · intro l' hl'
      rcases List.mem_append.1 hl' with hl' | hl'
      · obtain ⟨e', he', hk⟩ := h.done l' hl'
        exact ⟨e', hsub e' he', hk⟩
      · rw [List.mem_singleton] at hl'
        subst hl'
        exact ⟨(y, e.2 ++ [l']), List.mem_cons_self, by rw [hyv]⟩
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, h.nd⟩
      intro hm
      obtain ⟨x, hx, hxk⟩ := List.mem_map.1 hm
      have := List.any_eq_false.1 hany x hx
      simp [hxk] at this
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hN _ hy
      · exact h.bd x hx
    · intro k
      change (addKey t.mask (keyN y)).testBit (k + 64) = _
      rw [testBit_addKey, h.mb k, List.any_cons, Bool.or_comm]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]
    · exact hsub _ h.root
  · simp only [Bool.not_true]
    change t.mask.testBit (keyN y + 64) = true at hb
    refine ⟨h.split, h.cl, ?_, h.nd, h.bd, h.mb, h.root⟩
    intro l' hl'
    rcases List.mem_append.1 hl' with hl' | hl'
    · exact h.done l' hl'
    · rw [List.mem_singleton] at hl'
      subst hl'
      rw [h.mb, List.any_eq_true] at hb
      obtain ⟨x, hx, hxk⟩ := hb
      exact ⟨x, hx, by rw [hyv]; simpa using hxk⟩

theorem tj_fold (hN : ∀ c < 2 ^ 20, keyN c < N) {P : List (Nat × List α)} {e : Nat × List α} :
    ∀ (L D : List α) (t : BS α), TJ N keyN lc lets c0 P e D t →
      TJ N keyN lc lets c0 P e (D ++ L) (L.foldl (innerK keyN lc e.1 e.2) t)
  | [], D, t, h => by simpa using h
  | l :: L, D, t, h => by
    rw [List.foldl_cons, show D ++ l :: L = (D ++ [l]) ++ L by simp]
    exact tj_fold hN L (D ++ [l]) _ (tj_inner hN h l)

theorem ti_outer (hN : ∀ c < 2 ^ 20, keyN c < N) {r : Nat} {t : BS α}
    (h : TI N keyN lc lets c0 r t) : TI N keyN lc lets c0 (r + 1) (outerK keyN lc lets t) := by
  obtain ⟨P, hsplit, hlen, hcl⟩ := h.split
  obtain ⟨front, back, all, mask⟩ := t
  have hstep : ∀ (e : Nat × List α) (t1 : BS α), t1.all = all → t1.mask = mask →
      all.reverse = P ++ e :: queueOf t1 → P.length = r →
      TI N keyN lc lets c0 (r + 1) (lets.foldl (innerK keyN lc e.1 e.2) t1) := by
    intro e t1 ha hm hs hP
    have h0 : TJ N keyN lc lets c0 P e [] t1 := by
      refine ⟨by rw [ha]; exact hs, ?_, by simp, by rw [ha]; exact h.nd, by rw [ha]; exact h.bd,
        by rw [ha, hm]; exact h.mb, by rw [ha]; exact h.root⟩
      intro x hx
      rw [ha]
      exact hcl x hx
    have hj := tj_fold hN lets [] t1 h0
    simp only [List.nil_append] at hj
    refine ⟨⟨P ++ [e], by rw [hj.split]; simp, Or.inl (by simp [hP]), ?_⟩, hj.nd, hj.bd, hj.mb,
      hj.root⟩
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hj.cl x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact fun l hl => hj.done l hl
  unfold outerK
  simp only at hsplit hlen ⊢
  rcases front with _ | ⟨e, f⟩
  · rcases hbr : back.reverse with _ | ⟨e, f⟩
    · simp only
      refine ⟨⟨P, hsplit, Or.inr ?_, hcl⟩, h.nd, h.bd, h.mb, h.root⟩
      simp [queueOf, hbr]
    · simp only
      have hq : queueOf (BS.mk [] back all mask) = e :: f := by simp [queueOf, hbr]
      have hP : P.length = r := by
        rcases hlen with hlen | hlen
        · exact hlen
        · rw [hq] at hlen
          simp at hlen
      refine hstep e (BS.mk f [] all mask) rfl rfl ?_ hP
      rw [hsplit, hq]
      simp [queueOf]
  · simp only
    have hP : P.length = r := by
      rcases hlen with hlen | hlen
      · exact hlen
      · simp [queueOf] at hlen
    refine hstep e (BS.mk f back all mask) rfl rfl ?_ hP
    rw [hsplit]
    simp [queueOf]

theorem ti_loop (hN : ∀ c < 2 ^ 20, keyN c < N) : ∀ (n r : Nat) (t : BS α),
    TI N keyN lc lets c0 r t → TI N keyN lc lets c0 (r + n) (loopK keyN lc lets n t)
  | 0, r, t, h => h
  | n + 1, r, t, h => by
    have e : loopK keyN lc lets (n + 1) t = loopK keyN lc lets n (outerK keyN lc lets t) := by
      change letN (Nat.land (outerK keyN lc lets t).mask 1)
        (fun _ => loopK keyN lc lets n (outerK keyN lc lets t)) = _
      rw [letN_eq]
    rw [e, show r + (n + 1) = (r + 1) + n by omega]
    exact ti_loop hN n (r + 1) _ (ti_outer hN h)

theorem ti_init (hN : ∀ c < 2 ^ 20, keyN c < N) (h0 : c0 < 2 ^ 20) :
    TI N keyN lc lets c0 0
      (BS.mk [(c0, [])] [] [(c0, [])] (Nat.shiftLeft 1 (Nat.add (keyN c0) 64))) := by
  refine ⟨⟨[], by simp [queueOf], Or.inl rfl, by simp⟩, by simp, ?_, ?_, by simp⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact hN _ h0
  · intro k
    change (1 <<< (keyN c0 + 64)).testBit (k + 64) = _
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, Nat.add_right_cancel_iff, eq_comm]

theorem length_le_of_keys {L : List (Nat × List α)} (hnd : (L.map fun e => keyN e.1).Nodup)
    (hb : ∀ e ∈ L, keyN e.1 < N) : L.length ≤ N := by
  have h1 : (L.map fun e => keyN e.1).toFinset ⊆ Finset.range N := by
    intro k hk
    rw [List.mem_toFinset, List.mem_map] at hk
    obtain ⟨e, he, rfl⟩ := hk
    exact Finset.mem_range.2 (hb e he)
  have h2 := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hnd, List.length_map, Finset.card_range] at h2
  exact h2

theorem bfsT_closed (hN : ∀ c < 2 ^ 20, keyN c < N) (h0 : c0 < 2 ^ 20) {F : Nat} (hF : N ≤ F) :
    ∀ e ∈ (bfsT F keyN lc lets c0).all,
      Closed keyN lc lets (bfsT F keyN lc lets c0).all e := by
  have h := ti_loop (lets := lets) (lc := lc) hN F 0 _ (ti_init hN h0)
  rw [Nat.zero_add] at h
  change TI N keyN lc lets c0 F (bfsT F keyN lc lets c0) at h
  obtain ⟨P, hsplit, hlen, hcl⟩ := h.split
  have hq : queueOf (bfsT F keyN lc lets c0) = [] := by
    rcases hlen with hlen | hlen
    · by_contra hne
      have hl := length_le_of_keys h.nd h.bd
      have := congrArg List.length hsplit
      rw [List.length_reverse, List.length_append, hlen] at this
      have : 0 < (queueOf (bfsT F keyN lc lets c0)).length := List.length_pos_iff.2 hne
      omega
    · exact hlen
  rw [hq, List.append_nil] at hsplit
  intro e he
  exact hcl e (by rw [← hsplit, List.mem_reverse]; exact he)

theorem bfsT_root (hN : ∀ c < 2 ^ 20, keyN c < N) (h0 : c0 < 2 ^ 20) (F : Nat) :
    (c0, []) ∈ (bfsT F keyN lc lets c0).all := by
  have h := ti_loop (lets := lets) (lc := lc) hN F 0 _ (ti_init hN h0)
  exact h.root

end Inv

end CFSG.KC.M24L2
