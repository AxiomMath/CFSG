module

public import Certificates.Data.Kernel.L5.Greedy

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

open Subgroup

variable {n : Nat}

theorem length_le_of_nodup {l : List (Idx n)} (h : l.Nodup) : l.length ≤ n := by
  let _ : Fintype (Idx n) := Fintype.ofEquiv (Fin n) (Idx.equivFin n).symm
  have h2 : Fintype.card (Idx n) = n := by
    rw [Fintype.card_congr (Idx.equivFin n), Fintype.card_fin]
  have h3 := h.length_le_card
  omega

theorem mem_of_mul_closed {G : Type*} [Group G] [Finite G] {s T : Set G} (h1 : (1 : G) ∈ T)
    (hm : ∀ y ∈ T, ∀ g ∈ s, y * g ∈ T) {x : G} (hx : x ∈ closure s) : x ∈ T := by
  have hpow : ∀ g ∈ s, ∀ k : Nat, ∀ y ∈ T, y * g ^ k ∈ T := by
    intro g hg k
    induction k with
    | zero => simp
    | succ k ih =>
      intro y hy
      rw [pow_succ, ← mul_assoc]
      exact hm _ (ih y hy) g hg
  refine closure_induction_right (p := fun x _ => x ∈ T) h1 (fun y _ g hg hy => hm y hy g hg)
    (fun y _ g hg hy => ?_) hx
  have hpos := orderOf_pos g
  have hinv : g ^ (orderOf g - 1) = g⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [← hinv]
  exact hpow g hg _ y hy

variable [Group (Idx n)]

theorem evW_append_single (gs : List (Idx n)) (w : List Nat) (i : Nat) :
    evW gs (w ++ [i]) = evW gs w * gs.getD i 1 := by
  simp [evW, List.foldl_append]

theorem getD_mem_closure (gs : List (Idx n)) (i : Nat) :
    gs.getD i 1 ∈ closure {g | g ∈ gs} := by
  rw [List.getD_eq_getElem?_getD]
  cases h : gs[i]? with
  | none => exact one_mem _
  | some g => exact subset_closure (List.mem_of_getElem? h)

theorem evW_mem_closure (gs : List (Idx n)) (w : List Nat) :
    evW gs w ∈ closure {g | g ∈ gs} := by
  induction w using List.reverseRecOn with
  | nil => exact one_mem _
  | append_singleton w i ih =>
    rw [evW_append_single]
    exact mul_mem ih (getD_mem_closure gs i)

@[expose] def insW (st : Array Bool × List (Idx n × List Nat)) (c : Idx n × List Nat) :
    Array Bool × List (Idx n × List Nat) :=
  if st.1.getD c.1.v false then st else (st.1.set! c.1.v true, c :: st.2)

@[expose] def roundFn (gs : List (Idx n)) (st : Array Bool × List (Idx n × List Nat))
    (ew : Idx n × List Nat) : Array Bool × List (Idx n × List Nat) :=
  (List.range gs.length).foldl
    (fun (st : Array Bool × List (Idx n × List Nat)) (i : Nat) =>
      let e' := ew.1 * gs.getD i 1
      if st.1.getD e'.v false then st
      else (st.1.set! e'.v true, (e', ew.2 ++ [i]) :: st.2)) st

theorem roundFn_eq (gs : List (Idx n)) (st : Array Bool × List (Idx n × List Nat))
    (ew : Idx n × List Nat) :
    roundFn gs st ew =
      ((List.range gs.length).map fun i => (ew.1 * gs.getD i 1, ew.2 ++ [i])).foldl insW st := by
  rw [List.foldl_map]
  rfl

def InsInv (gs : List (Idx n)) (A : List (Idx n × List Nat))
    (st : Array Bool × List (Idx n × List Nat)) : Prop :=
  st.1.size = n ∧ (∀ x : Idx n, st.1.getD x.v false = true ↔ x ∈ (A ++ st.2).map Prod.fst) ∧
    ((A ++ st.2).map Prod.fst).Nodup ∧ ∀ p ∈ st.2, evW gs p.2 = p.1

theorem getD_set_true (a : Array Bool) (i j : Nat) (hi : i < a.size) :
    (a.set! i true).getD j false = if i = j then true else a.getD j false := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split <;> simp_all

theorem insW_spec {gs : List (Idx n)} {A : List (Idx n × List Nat)}
    {st : Array Bool × List (Idx n × List Nat)} (h : InsInv gs A st) {c : Idx n × List Nat}
    (hc : evW gs c.2 = c.1) :
    InsInv gs A (insW st c) ∧ c.1 ∈ (A ++ (insW st c).2).map Prod.fst ∧
      ∀ x, x ∈ (A ++ st.2).map Prod.fst → x ∈ (A ++ (insW st c).2).map Prod.fst := by
  obtain ⟨hs, hv, hnd, hw⟩ := h
  unfold insW
  split
  · next hc1 => exact ⟨⟨hs, hv, hnd, hw⟩, (hv c.1).1 hc1, fun x hx => hx⟩
  · next hc1 =>
    have hcn : c.1 ∉ (A ++ st.2).map Prod.fst := fun hm => hc1 ((hv c.1).2 hm)
    have hlt : c.1.v < st.1.size := by
      rw [hs]
      exact c.1.v_lt
    have hmem : ∀ x, x ∈ (A ++ (c :: st.2)).map Prod.fst ↔
        x = c.1 ∨ x ∈ (A ++ st.2).map Prod.fst := by
      intro x
      simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
      tauto
    refine ⟨⟨?_, ?_, ?_, ?_⟩, (hmem _).2 (Or.inl rfl), fun x hx => (hmem x).2 (Or.inr hx)⟩
    · simp [Array.set!, hs]
    · intro x
      rw [getD_set_true _ _ _ hlt, hmem]
      by_cases hx : x = c.1
      · subst hx
        simp
      · have hne : c.1.v ≠ x.v := fun h => hx (Idx.ext h.symm)
        rw [if_neg hne, hv x]
        simp [hx]
    · have hp : ((A ++ c :: st.2).map Prod.fst).Perm (c.1 :: (A ++ st.2).map Prod.fst) := by
        simp
      exact hp.nodup_iff.2 (List.nodup_cons.2 ⟨hcn, hnd⟩)
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hc
      · exact hw p hp

theorem foldl_insW {gs : List (Idx n)} {A : List (Idx n × List Nat)} :
    ∀ (cs : List (Idx n × List Nat)) (st : Array Bool × List (Idx n × List Nat)),
      InsInv gs A st → (∀ c ∈ cs, evW gs c.2 = c.1) →
      InsInv gs A (cs.foldl insW st) ∧
        (∀ c ∈ cs, c.1 ∈ (A ++ (cs.foldl insW st).2).map Prod.fst) ∧
        ∀ x, x ∈ (A ++ st.2).map Prod.fst → x ∈ (A ++ (cs.foldl insW st).2).map Prod.fst
  | [], st, h, _ => ⟨h, by simp, fun _ hx => hx⟩
  | c :: cs, st, h, hcs => by
    obtain ⟨h1, h2, h3⟩ := insW_spec h (hcs c (by simp))
    obtain ⟨k1, k2, k3⟩ := foldl_insW cs _ h1 (fun c' hc' => hcs c' (by simp [hc']))
    refine ⟨k1, ?_, fun x hx => k3 x (h3 x hx)⟩
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact k3 _ h2
    · exact k2 c' hc'

theorem roundFn_spec {gs : List (Idx n)} {A : List (Idx n × List Nat)}
    (st : Array Bool × List (Idx n × List Nat)) (h : InsInv gs A st) (ew : Idx n × List Nat)
    (hew : evW gs ew.2 = ew.1) :
    InsInv gs A (roundFn gs st ew) ∧
      (∀ g ∈ gs, ew.1 * g ∈ (A ++ (roundFn gs st ew).2).map Prod.fst) ∧
      ∀ x, x ∈ (A ++ st.2).map Prod.fst → x ∈ (A ++ (roundFn gs st ew).2).map Prod.fst := by
  rw [roundFn_eq]
  obtain ⟨k1, k2, k3⟩ :=
    foldl_insW ((List.range gs.length).map fun i => (ew.1 * gs.getD i 1, ew.2 ++ [i])) st h (by
    intro c hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    rw [evW_append_single, hew])
  refine ⟨k1, ?_, k3⟩
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
  have := k2 (ew.1 * gs.getD i 1, ew.2 ++ [i]) (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using this

theorem foldl_roundFn {gs : List (Idx n)} {A : List (Idx n × List Nat)} :
    ∀ (F : List (Idx n × List Nat)) (st : Array Bool × List (Idx n × List Nat)),
      InsInv gs A st → (∀ ew ∈ F, evW gs ew.2 = ew.1) →
      InsInv gs A (F.foldl (roundFn gs) st) ∧
        (∀ ew ∈ F, ∀ g ∈ gs, ew.1 * g ∈ (A ++ (F.foldl (roundFn gs) st).2).map Prod.fst) ∧
        ∀ x, x ∈ (A ++ st.2).map Prod.fst → x ∈ (A ++ (F.foldl (roundFn gs) st).2).map Prod.fst
  | [], st, h, _ => ⟨h, by simp, fun _ hx => hx⟩
  | ew :: F, st, h, hF => by
    obtain ⟨h1, h2, h3⟩ := roundFn_spec st h ew (hF ew (by simp))
    obtain ⟨k1, k2, k3⟩ := foldl_roundFn F _ h1 (fun c hc => hF c (by simp [hc]))
    refine ⟨k1, ?_, fun x hx => k3 x (h3 x hx)⟩
    intro c hc g hg
    rcases List.mem_cons.1 hc with rfl | hc
    · exact k3 _ (h2 g hg)
    · exact k2 c hc g hg

def WOut (gs : List (Idx n)) (A R : List (Idx n × List Nat)) : Prop :=
  (∀ p ∈ R, evW gs p.2 = p.1) ∧ (∀ p ∈ R, ∀ g ∈ gs, p.1 * g ∈ R.map Prod.fst) ∧
    ∀ x ∈ A.map Prod.fst, x ∈ R.map Prod.fst

theorem wordsGo_succ_cons (gs : List (Idx n)) (fuel : Nat) (vis : Array Bool)
    (f : Idx n × List Nat) (F A : List (Idx n × List Nat)) :
    wordsGo gs (fuel + 1) vis (f :: F) A =
      wordsGo gs fuel ((f :: F).foldl (roundFn gs) (vis, [])).1
        ((f :: F).foldl (roundFn gs) (vis, [])).2.reverse
        (A ++ ((f :: F).foldl (roundFn gs) (vis, [])).2.reverse) := rfl

theorem wordsGo_spec (gs : List (Idx n)) :
    ∀ (fuel : Nat) (vis : Array Bool) (F A : List (Idx n × List Nat)),
      vis.size = n → (∀ x : Idx n, vis.getD x.v false = true ↔ x ∈ A.map Prod.fst) →
      (A.map Prod.fst).Nodup → (∀ p ∈ A, evW gs p.2 = p.1) → (∀ p ∈ F, p ∈ A) →
      (∀ p ∈ A, p.1 ∉ F.map Prod.fst → ∀ g ∈ gs, p.1 * g ∈ A.map Prod.fst) →
      (F ≠ [] → n + 1 ≤ A.length + fuel) →
      WOut gs A (wordsGo gs fuel vis F A)
  | fuel, vis, [], A, _, _, _, hw, _, hcl, _ => by
    cases fuel <;> exact ⟨hw, fun p hp g hg => hcl p hp (by simp) g hg, fun _ hx => hx⟩
  | 0, vis, f :: F, A, _, _, hnd, _, _, _, hlen => by
    have h1 := hlen (by simp)
    have h2 := length_le_of_nodup hnd
    simp only [List.length_map] at h2
    omega
  | fuel + 1, vis, f :: F, A, hs, hv, hnd, hw, hF, hcl, hlen => by
    have h0 : InsInv gs A (vis, []) := ⟨hs, by simpa using hv, by simpa using hnd, by simp⟩
    have hround := foldl_roundFn (f :: F) (vis, []) h0 (fun ew hew => hw ew (hF ew hew))
    rw [wordsGo_succ_cons]
    generalize (f :: F).foldl (roundFn gs) (vis, []) = st at hround ⊢
    obtain ⟨V, N⟩ := st
    obtain ⟨⟨k1, k2, k3, k4⟩, kcl, kmono⟩ := hround
    simp only at k1 k2 k3 k4 kcl kmono ⊢
    have hmr : ∀ x, x ∈ (A ++ N.reverse).map Prod.fst ↔ x ∈ (A ++ N).map Prod.fst := by
      intro x
      simp
    have hA : ∀ x ∈ A.map Prod.fst, x ∈ (A ++ N.reverse).map Prod.fst := fun x hx =>
      (hmr x).2 (kmono x (by simpa using hx))
    have ih := wordsGo_spec gs fuel V N.reverse (A ++ N.reverse) k1
      (fun x => (k2 x).trans (hmr x).symm)
      (((List.Perm.append_left A (List.reverse_perm N)).map Prod.fst).nodup_iff.2 k3)
      (by
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact hw p hp
        · exact k4 p (List.mem_reverse.1 hp))
      (fun p hp => List.mem_append_right A hp)
      (by
        intro p hp hpF g hg
        rcases List.mem_append.1 hp with hpA | hpN
        · by_cases hpf : p.1 ∈ (f :: F).map Prod.fst
          · obtain ⟨ew, hew, he⟩ := List.mem_map.1 hpf
            rw [← he]
            exact (hmr _).2 (kcl ew hew g hg)
          · exact hA _ (hcl p hpA hpf g hg)
        · exact absurd (List.mem_map_of_mem hpN) hpF)
      (by
        intro hN
        have h1 := hlen (by simp)
        cases N with
        | nil => simp at hN
        | cons a l =>
          simp only [List.length_append, List.length_reverse, List.length_cons]
          omega)
    exact ⟨ih.1, ih.2.1, fun x hx => ih.2.2 x (hA x hx)⟩

theorem wordsOf_spec (gs : List (Idx n)) : WOut gs [(1, [])] (wordsOf gs) := by
  have hlt : (1 : Idx n).v < (Array.replicate n false).size := by simpa using (1 : Idx n).v_lt
  refine wordsGo_spec gs n _ _ _ (by simp [Array.set!]) ?_ (by simp) (by simp [evW]) (by simp)
    ?_ (fun _ => by simp)
  · intro x
    rw [getD_set_true _ _ _ hlt]
    by_cases hx : x = 1
    · subst hx
      simp
    · have hne : (1 : Idx n).v ≠ x.v := fun h => hx (Idx.ext h.symm)
      rw [if_neg hne, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> simp [hx]
  · intro p hp hpF
    simp only [List.mem_singleton] at hp
    subst hp
    simp at hpF

theorem mem_wordsOf_iff (gs : List (Idx n)) (x : Idx n) :
    x ∈ (wordsOf gs).map Prod.fst ↔ x ∈ closure {g | g ∈ gs} := by
  obtain ⟨hw, hcl, h1⟩ := wordsOf_spec gs
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    rw [← hw p hp]
    exact evW_mem_closure gs p.2
  · intro hx
    refine mem_of_mul_closed (T := {y | y ∈ (wordsOf gs).map Prod.fst}) (h1 1 (by simp)) ?_ hx
    intro y hy g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
    exact hcl p hp g hg

theorem evW_wordsOf (gs : List (Idx n)) (p : Idx n × List Nat) (hp : p ∈ wordsOf gs) :
    evW gs p.2 = p.1 :=
  (wordsOf_spec gs).1 p hp

theorem any_wordsOf_iff (gs : List (Idx n)) (s : Idx n) :
    ((wordsOf gs).any fun p => decide (p.1 = s)) = true ↔ s ∈ closure {g | g ∈ gs} := by
  rw [← mem_wordsOf_iff]
  simp [List.any_eq_true, List.mem_map]

theorem mem_of_subChk (gs : List (Idx n)) (W : List (Idx n × List Nat))
    (h : subChk gs W = true) (x : Idx n) :
    x ∈ W.map Prod.fst ↔ x ∈ closure {g | g ∈ gs} := by
  simp only [subChk, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨h1, hcl⟩, hw⟩ := h
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    rw [← hw p hp]
    exact evW_mem_closure gs p.2
  · intro hx
    refine mem_of_mul_closed (T := {y | y ∈ W.map Prod.fst}) h1 ?_ hx
    intro y hy g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
    exact hcl p hp g hg

omit [Group (Idx n)] in
theorem greedyStep_false (R : List (Idx n)) (Ls : List (List (Idx n))) :
    ∀ (S : List (Idx n)) (j : Nat), (S.foldl (greedyStep R Ls) (j, false)).2 = false
  | [], _ => rfl
  | s :: S, j => by
    simp only [List.foldl_cons, greedyStep]
    split
    · exact greedyStep_false R Ls S j
    · simpa using greedyStep_false R Ls S (j + 1)

theorem greedyGens_aux (init R : List (Idx n)) (Ls : List (List (Idx n)))
    (hL : ∀ j ≤ R.length, ∀ x, x ∈ Ls.getD j [] ↔ x ∈ closure {g | g ∈ init ++ R.take j}) :
    ∀ (S : List (Idx n)) (j : Nat) (b : Bool), j ≤ R.length →
      (S.foldl (greedyStep R Ls) (j, b)).2 = true →
      S.foldl (fun gs s => if (wordsOf gs).any (fun p => decide (p.1 = s)) then gs else gs ++ [s])
          (init ++ R.take j) = init ++ R.take (S.foldl (greedyStep R Ls) (j, b)).1
  | [], _, _, _, _ => rfl
  | s :: S, j, b, hj, h => by
    simp only [List.foldl_cons, greedyStep] at h ⊢
    by_cases hc : (Ls.getD j []).contains s = true
    · rw [if_pos hc] at h ⊢
      have hs : ((wordsOf (init ++ R.take j)).any fun p => decide (p.1 = s)) = true := by
        rw [any_wordsOf_iff, ← hL j hj]
        simpa using hc
      rw [if_pos hs]
      exact greedyGens_aux init R Ls hL S j b hj h
    · rw [if_neg hc] at h ⊢
      have hs : ¬ ((wordsOf (init ++ R.take j)).any fun p => decide (p.1 = s)) = true := by
        rw [any_wordsOf_iff, ← hL j hj]
        simpa using hc
      rw [if_neg hs]
      have hb : (b && decide (R[j]? = some s)) = true := by
        by_contra hb
        rw [Bool.not_eq_true] at hb
        rw [hb, greedyStep_false] at h
        exact Bool.false_ne_true h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨rfl, hR⟩ := hb
      have hjl : j < R.length := by
        by_contra hjl
        rw [List.getElem?_eq_none (by omega)] at hR
        exact absurd hR (by simp)
      have htake : R.take (j + 1) = R.take j ++ [s] := by
        rw [List.take_succ, hR]
        rfl
      simp only [hR, decide_true, Bool.and_self] at h ⊢
      rw [List.append_assoc, ← htake]
      exact greedyGens_aux init R Ls hL S (j + 1) true hjl h

theorem greedyGens_eq (S init R : List (Idx n)) (Ls : List (List (Idx n)))
    (hL : ∀ j ≤ R.length, ∀ x, x ∈ Ls.getD j [] ↔ x ∈ closure {g | g ∈ init ++ R.take j})
    (h : greedySim S R Ls = true) : greedyGens S init = init ++ R := by
  simp only [greedySim, Bool.and_eq_true, decide_eq_true_eq] at h
  have := greedyGens_aux init R Ls hL S 0 true (Nat.zero_le _) h.1
  rw [h.2, List.take_length, List.take_zero, List.append_nil] at this
  exact this

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end
