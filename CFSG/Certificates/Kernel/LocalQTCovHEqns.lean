module

public import CFSG.Certificates.Kernel.LocalQTCovHBase
import CFSG.Certificates.Kernel.LocalQTCovTTri

public section

namespace CFSG.KC.LQT.Cov.H

open CFSG.KC.LQT.Cov CFSG.QuasithinUnique.Ch1.HSCover
open CFSG.QuasithinUnique.Ch1.M22Cover (CayTab Letter fo posW invW)
open CFSG.QuasithinUnique.Ch1.TitsCover (formOf)
open CFSG.KC.LQT.Cov.Eqns (andB_eq notB_eq letNN_eq eqL_iff allBs_cons allBs_nil
  forall₂_map_map toArray_getElem! map_val_map_fo)

variable {d : CH}

private theorem eqnsH_tab_word (v : Nat) :
    (ofCH d).tab.word v = (d.words.getD v []).map fo := by
  show (d.words.toArray[v]!).map fo = _
  rw [toArray_getElem!]
  rfl

private theorem eqnsH_tab_tgt (v : Nat) (i : Fin 3) :
    (ofCH d).tab.tgt v i = d.tgt.getD (3 * v + i) 0 := by
  show d.tgt.toArray[3 * v + (i : Nat)]! = _
  rw [toArray_getElem!]
  rfl

private theorem eqnsH_tab_back (v : Nat) (i : Fin 3) :
    (ofCH d).tab.back v i = d.back.getD (3 * v + i) 0 := by
  show d.back.toArray[3 * v + (i : Nat)]! = _
  rw [toArray_getElem!]
  rfl

private theorem eqnsH_words_lt (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3) (k : Nat) :
    ∀ l ∈ d.words.getD k [], l < 3 := by
  intro l hl
  rw [List.getD_eq_getElem?_getD] at hl
  cases h : d.words[k]? with
  | none => simp [h] at hl
  | some w =>
    rw [h, Option.getD_some] at hl
    exact hw w (List.mem_of_getElem? h) l hl

private def eqnsH_cvL (l : Nat × Bool) : Letter := (fo l.1, l.2)

private theorem eqnsH_fo_val_of_lt {i : Nat} (hi : i < 3) : ((fo i : Fin 3) : Nat) = i :=
  Nat.mod_eq_of_lt hi

private theorem eqnsH_step_eq (v : Nat) (l : Nat × Bool) (hl : l.1 < 3) :
    (ofCH d).tab.step v (eqnsH_cvL l) = stepH (rowsG d.tgt) (rowsG d.back) v l := by
  obtain ⟨i, s⟩ := l
  have hfo := eqnsH_fo_val_of_lt (i := i) hl
  have hfoFin : (fo i : Fin 3) = ⟨i, hl⟩ := Fin.ext (by simpa using hfo)
  cases s
  · change (ofCH d).tab.back v (fo i) = getRG (rowsG d.back) (3 * v + i) 0
    rw [eqnsH_tab_back, T.getRG_rowsG, hfoFin]
  · change (ofCH d).tab.tgt v (fo i) = getRG (rowsG d.tgt) (3 * v + i) 0
    rw [eqnsH_tab_tgt, T.getRG_rowsG, hfoFin]

private theorem eqnsH_edge_eq (v : Nat) (l : Nat × Bool) (hl : l.1 < 3) :
    (ofCH d).tab.edge v (eqnsH_cvL l) = edgeH (rowsG d.back) v l := by
  obtain ⟨i, s⟩ := l
  have hfo := eqnsH_fo_val_of_lt (i := i) hl
  cases s
  · change 3 * (ofCH d).tab.back v (fo i) + (fo i : Nat) =
      3 * getRG (rowsG d.back) (3 * v + i) 0 + i
    rw [eqnsH_tab_back, T.getRG_rowsG, hfo]
  · change 3 * v + (fo i : Nat) = 3 * v + i
    rw [hfo]

private noncomputable def eqnsH_walkF (w : List (Nat × Bool)) : Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun f v => (f, v))
    (fun l _ ih f v => letNN (Nat.xor f (Nat.pow 2 (edgeH (rowsG d.back) v l))) fun f' =>
      letNN (stepH (rowsG d.tgt) (rowsG d.back) v l) fun v' => ih f' v') w

private theorem eqnsH_walkF_eq :
    ∀ (w : List (Nat × Bool)), (∀ l ∈ w, l.1 < 3) → ∀ f v : Nat,
      eqnsH_walkF (d := d) w f v = (((ofCH d).tab.walkEdges v (w.map eqnsH_cvL)).foldl
        (fun f e => f ^^^ 2 ^ e) f, (ofCH d).tab.walkEnd v (w.map eqnsH_cvL))
  | [], _, _, _ => rfl
  | l :: w, hw, f, v => by
    have hl := hw l List.mem_cons_self
    have e : eqnsH_walkF (d := d) (l :: w) f v =
        eqnsH_walkF (d := d) w (f ^^^ 2 ^ edgeH (rowsG d.back) v l)
          (stepH (rowsG d.tgt) (rowsG d.back) v l) := by
      change letNN _ (fun f' => letNN _ (fun v' => eqnsH_walkF (d := d) w f' v')) = _
      rw [letNN_eq, letNN_eq]
      rfl
    rw [e, eqnsH_walkF_eq w (fun l' h => hw l' (List.mem_cons_of_mem _ h))]
    simp only [List.map_cons, CayTab.walkEdges, CayTab.walkEnd, List.foldl_cons,
      eqnsH_step_eq v l hl, eqnsH_edge_eq v l hl]

private theorem eqnsH_walkH_eq (v : Nat) (w : List (Nat × Bool)) (hw : ∀ l ∈ w, l.1 < 3) :
    walkH (rowsG d.tgt) (rowsG d.back) v w =
      (formOf ((ofCH d).tab.walkEdges v (w.map eqnsH_cvL)),
        (ofCH d).tab.walkEnd v (w.map eqnsH_cvL)) :=
  eqnsH_walkF_eq w hw 0 v

private theorem eqnsH_map_posK (W : List Nat) : (posK W).map eqnsH_cvL = posW (W.map fo) := by
  simp only [posK, posW, eqnsH_cvL, List.map_map, Function.comp_def]

private theorem eqnsH_map_invWK (W : List Nat) :
    (invWK W).map eqnsH_cvL = invW (W.map fo) := by
  simp only [invWK, invW, eqnsH_cvL, List.map_map, Function.comp_def, List.map_reverse]

private theorem eqnsH_posK_lt {W : List Nat} (hW : ∀ x ∈ W, x < 3) :
    ∀ l ∈ posK W, l.1 < 3 := by
  intro l hl
  unfold posK at hl
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
  exact hW x hx

private theorem eqnsH_invWK_lt {W : List Nat} (hW : ∀ x ∈ W, x < 3) :
    ∀ l ∈ invWK W, l.1 < 3 := by
  intro l hl
  unfold invWK at hl
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
  exact hW x (List.mem_reverse.1 hx)

private theorem eqnsH_wordsK_lt (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3) (k : Nat) :
    ∀ l ∈ getRG (rowsG d.words) k [], l < 3 := by
  rw [T.getRG_rowsG]
  exact eqnsH_words_lt hw k

private theorem eqnsH_sqH_eq (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3) (v : Nat) :
    sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) v =
      (formOf (sqEdgesOf (ofCH d).tab v),
        (ofCH d).tab.walkEnd v (posW ((ofCH d).tab.word v))) := by
  unfold sqH
  rw [eqnsH_walkH_eq v _ (eqnsH_posK_lt (eqnsH_wordsK_lt hw v)), eqnsH_map_posK, T.getRG_rowsG,
    sqEdgesOf, eqnsH_tab_word]

private def eqnsH_cvE (p : Nat × Fin 3) : Nat × Nat := (p.1, p.2)

private def eqnsH_edgesK (n : Nat) : List (Nat × Nat) :=
  (List.map (fun v => List.map (fun i => (v, i)) [0, 1, 2]) (List.range n)).flatten

private def eqnsH_edgesN (n : Nat) : List (Nat × Fin 3) :=
  (List.range n).flatMap fun v => (List.finRange 3).map fun i => (v, i)

private theorem eqnsH_edgesK_eq (n : Nat) :
    eqnsH_edgesK n = (eqnsH_edgesN n).map eqnsH_cvE := by
  unfold eqnsH_edgesK eqnsH_edgesN
  rw [List.map_flatMap, List.flatMap_def]
  congr 1

private noncomputable def eqnsH_isTK (p : Nat × Nat) : Bool :=
  CFSG.KC.LQT.Syl.eqL (getRG (rowsG d.words) (getRG (rowsG d.tgt) (3 * p.1 + p.2) 0) [])
    (getRG (rowsG d.words) p.1 [] ++ [p.2])

private def eqnsH_isTN (p : Nat × Fin 3) : Bool :=
  (ofCH d).tab.word ((ofCH d).tab.tgt p.1 p.2) == ((ofCH d).tab.word p.1 ++ [p.2])

private theorem eqnsH_isTK_eq (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3) (p : Nat × Fin 3) :
    eqnsH_isTK (d := d) (eqnsH_cvE p) = eqnsH_isTN (d := d) p := by
  have hwk := eqnsH_words_lt hw p.1
  rw [Bool.eq_iff_iff]
  unfold eqnsH_isTK eqnsH_isTN eqnsH_cvE
  simp only [eqL_iff, beq_iff_eq, eqnsH_tab_word, eqnsH_tab_tgt, T.getRG_rowsG]
  have h3 : ([p.2] : List (Fin 3)) = [(p.2 : Nat)].map fo := by simp [fo_val]
  have hlt : ∀ x ∈ d.words.getD p.1 [] ++ [(p.2 : Nat)], x < 3 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hwk x hx
    · rw [List.mem_singleton.1 hx]
      exact p.2.2
  rw [h3, ← List.map_append]
  constructor
  · intro h
    rw [h]
  · intro h
    have := congrArg (List.map Fin.val) h
    have hwk' := eqnsH_words_lt hw (d.tgt.getD (3 * p.1 + p.2) 0)
    rwa [map_val_map_fo _ hwk', map_val_map_fo _ hlt] at this

private def eqnsH_Rel (q : Bool × Nat) (e : Eqn) : Prop :=
  q.2 = e.form (ofCH d) ∧ (0 < d.nV → q.1 = true → e.valid (ofCH d) = true)

private theorem eqnsH_rel_tree (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3) :
    List.Forall₂ (eqnsH_Rel (d := d))
      ((List.filter (eqnsH_isTK (d := d)) (eqnsH_edgesK d.nV)).map fun p =>
        (Nat.blt p.1 d.nV, Nat.pow 2 (3 * p.1 + p.2)))
      ((List.filter (eqnsH_isTN (d := d)) (eqnsH_edgesN d.nV)).map fun p =>
        Eqn.tree p.1 p.2) := by
  have hf : List.filter (eqnsH_isTK (d := d) ∘ eqnsH_cvE) (eqnsH_edgesN d.nV) =
      List.filter (eqnsH_isTN (d := d)) (eqnsH_edgesN d.nV) :=
    List.filter_congr fun p _ => eqnsH_isTK_eq hw p
  rw [eqnsH_edgesK_eq, List.filter_map, hf, List.map_map]
  refine forall₂_map_map fun p hp => ⟨rfl, fun _ hb => ?_⟩
  have hT : eqnsH_isTN (d := d) p = true := (List.mem_filter.1 hp).2
  change (decide (p.1 < d.nV) && eqnsH_isTN (d := d) p) = true
  rw [hT, Bool.and_true, decide_eq_true_eq]
  exact Nat.blt_eq.mp hb

private noncomputable def eqnsH_wTK (p : Nat × Nat) : List (Nat × Bool) :=
  posK (getRG (rowsG d.words) p.1 []) ++ [(p.2, true)] ++
    invWK (getRG (rowsG d.words) (getRG (rowsG d.tgt) (3 * p.1 + p.2) 0) [])

private def eqnsH_wTN (p : Nat × Fin 3) : List Letter :=
  posW ((ofCH d).tab.word p.1) ++ [(p.2, true)] ++
    invW ((ofCH d).tab.word ((ofCH d).tab.tgt p.1 p.2))

private theorem eqnsH_map_wTK (p : Nat × Fin 3) :
    (eqnsH_wTK (d := d) (eqnsH_cvE p)).map eqnsH_cvL = eqnsH_wTN (d := d) p := by
  unfold eqnsH_wTK eqnsH_wTN eqnsH_cvE
  simp only [List.map_append, eqnsH_map_posK, eqnsH_map_invWK, eqnsH_tab_word, eqnsH_tab_tgt,
    T.getRG_rowsG, List.map_cons, List.map_nil, eqnsH_cvL, fo_val]

private theorem eqnsH_wTK_lt (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3) (p : Nat × Fin 3) :
    ∀ l ∈ eqnsH_wTK (d := d) (eqnsH_cvE p), l.1 < 3 := by
  intro l hl
  unfold eqnsH_wTK at hl
  rcases List.mem_append.1 hl with hl | hl
  · rcases List.mem_append.1 hl with hl | hl
    · exact eqnsH_posK_lt (eqnsH_wordsK_lt hw _) l hl
    · rw [List.mem_singleton.1 hl]
      exact p.2.2
  · exact eqnsH_invWK_lt (eqnsH_wordsK_lt hw _) l hl

private noncomputable def eqnsH_transK (p : Nat × Nat) (j : Nat) : Bool × Nat :=
  (CFSG.KC.LQT.S.allBs [Nat.blt (getRG (rowsG d.tgt) j 0) d.nV,
      Nat.beq (walkH (rowsG d.tgt) (rowsG d.back) 0 (eqnsH_wTK (d := d) p)).2 0,
      Nat.beq (walkH (rowsG d.tgt) (rowsG d.back) (getRG (rowsG d.tgt) j 0)
        (eqnsH_wTK (d := d) p)).2 (getRG (rowsG d.tgt) j 0)],
    Nat.xor (walkH (rowsG d.tgt) (rowsG d.back) 0 (eqnsH_wTK (d := d) p)).1
      (walkH (rowsG d.tgt) (rowsG d.back) (getRG (rowsG d.tgt) j 0) (eqnsH_wTK (d := d) p)).1)

private theorem eqnsH_rel_trans (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3) :
    List.Forall₂ (eqnsH_Rel (d := d))
      ((List.filter (fun p => CFSG.KC.Ord.notB (eqnsH_isTK (d := d) p))
        (eqnsH_edgesK d.nV)).map fun p => [0, 1, 2].map (eqnsH_transK (d := d) p)).flatten
      ((List.filter (fun p => !eqnsH_isTN (d := d) p) (eqnsH_edgesN d.nV)).flatMap fun p =>
        (List.finRange 3).map fun j =>
          Eqn.trans (eqnsH_wTN (d := d) p) 0 ((ofCH d).tab.tgt 0 j)) := by
  have hf : List.filter ((fun p => CFSG.KC.Ord.notB (eqnsH_isTK (d := d) p)) ∘ eqnsH_cvE)
      (eqnsH_edgesN d.nV) = List.filter (fun p => !eqnsH_isTN (d := d) p) (eqnsH_edgesN d.nV) :=
    List.filter_congr fun p _ => by rw [Function.comp_apply, notB_eq, eqnsH_isTK_eq hw p]
  rw [eqnsH_edgesK_eq, List.filter_map, hf, List.map_map, List.flatMap_def]
  refine List.rel_flatten (forall₂_map_map fun p _ => ?_)
  have h012 : ([0, 1, 2] : List Nat) = (List.finRange 3).map Fin.val := rfl
  rw [Function.comp_apply, h012, List.map_map]
  refine forall₂_map_map fun j _ => ?_
  have hwl := eqnsH_wTK_lt hw p
  have h0 : (ofCH d).tab.tgt 0 j = getRG (rowsG d.tgt) j 0 := by
    simp [eqnsH_tab_tgt, T.getRG_rowsG]
  refine ⟨?_, fun hn hb => ?_⟩
  · change Nat.xor (walkH (rowsG d.tgt) (rowsG d.back) 0 (eqnsH_wTK (d := d) (eqnsH_cvE p))).1
        (walkH (rowsG d.tgt) (rowsG d.back) (getRG (rowsG d.tgt) j 0)
          (eqnsH_wTK (d := d) (eqnsH_cvE p))).1 =
      formOf ((ofCH d).tab.walkEdges 0 (eqnsH_wTN (d := d) p)) ^^^
        formOf ((ofCH d).tab.walkEdges ((ofCH d).tab.tgt 0 j) (eqnsH_wTN (d := d) p))
    rw [eqnsH_walkH_eq _ _ hwl, eqnsH_walkH_eq _ _ hwl, eqnsH_map_wTK, h0]
    rfl
  · change CFSG.KC.LQT.S.allBs [Nat.blt (getRG (rowsG d.tgt) j 0) d.nV,
      Nat.beq (walkH (rowsG d.tgt) (rowsG d.back) 0 (eqnsH_wTK (d := d) (eqnsH_cvE p))).2 0,
      Nat.beq (walkH (rowsG d.tgt) (rowsG d.back) (getRG (rowsG d.tgt) j 0)
        (eqnsH_wTK (d := d) (eqnsH_cvE p))).2 (getRG (rowsG d.tgt) j 0)] = true at hb
    rw [eqnsH_walkH_eq _ _ hwl, eqnsH_walkH_eq _ _ hwl, eqnsH_map_wTK, ← h0] at hb
    simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true, Nat.blt_eq,
      Nat.beq_eq] at hb
    change (decide (0 < d.nV) && decide ((ofCH d).tab.tgt 0 j < d.nV) &&
      ((ofCH d).tab.walkEnd 0 (eqnsH_wTN (d := d) p) == 0) &&
      ((ofCH d).tab.walkEnd ((ofCH d).tab.tgt 0 j) (eqnsH_wTN (d := d) p) ==
        (ofCH d).tab.tgt 0 j)) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨hn, hb.1⟩, hb.2.1⟩, hb.2.2⟩

private noncomputable def eqnsH_pairK (r : List Nat × Nat × Nat) : Bool × Nat :=
  (CFSG.KC.LQT.S.allBs [Nat.blt r.2.1 d.nV, Nat.blt r.2.2 d.nV,
      Nat.beq (sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) r.2.1).2 0,
      Nat.beq (sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) r.2.2).2 0],
    Nat.xor (sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) r.2.1).1
      (sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) r.2.2).1)

private theorem eqnsH_rel_pairs (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3) :
    List.Forall₂ (eqnsH_Rel (d := d)) (d.pairs.map (eqnsH_pairK (d := d)))
      ((ofCH d).pairs.map fun r => Eqn.eqv r.a r.b) := by
  change List.Forall₂ _ _ ((d.pairs.map fun p =>
    ({ gw := p.1, a := p.2.1, b := p.2.2 } : Rec)).map fun r => Eqn.eqv r.a r.b)
  rw [List.map_map]
  refine forall₂_map_map fun r hr => ⟨?_, fun _ hb => ?_⟩
  · change Nat.xor (sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) r.2.1).1
        (sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) r.2.2).1 =
      formOf (sqEdgesOf (ofCH d).tab r.2.1) ^^^ formOf (sqEdgesOf (ofCH d).tab r.2.2)
    rw [eqnsH_sqH_eq hw r.2.1, eqnsH_sqH_eq hw r.2.2]
    rfl
  · change CFSG.KC.LQT.S.allBs [Nat.blt r.2.1 d.nV, Nat.blt r.2.2 d.nV,
      Nat.beq (sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) r.2.1).2 0,
      Nat.beq (sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) r.2.2).2 0] = true at hb
    rw [eqnsH_sqH_eq hw r.2.1, eqnsH_sqH_eq hw r.2.2] at hb
    simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true, Nat.blt_eq,
      Nat.beq_eq] at hb
    have hany : (ofCH d).pairs.any (fun r' => r'.a == r.2.1 && r'.b == r.2.2) = true :=
      List.any_eq_true.2 ⟨_, List.mem_map_of_mem hr, by simp⟩
    change (decide (r.2.1 < d.nV) && decide (r.2.2 < d.nV) &&
      ((ofCH d).tab.walkEnd r.2.1 (posW ((ofCH d).tab.word r.2.1)) == 0) &&
      ((ofCH d).tab.walkEnd r.2.2 (posW ((ofCH d).tab.word r.2.2)) == 0) &&
      (ofCH d).pairs.any (fun r' => r'.a == r.2.1 && r'.b == r.2.2)) = true
    rw [hany, Bool.and_true]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨hb.1, hb.2.1⟩, hb.2.2.1⟩, hb.2.2.2⟩

private noncomputable def eqnsH_anchorK (r : List Nat × Nat) : Bool × Nat :=
  (CFSG.KC.Ord.andB (Nat.blt r.2 d.nV)
      (Nat.beq (sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) r.2).2 0),
    (sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) r.2).1)

private theorem eqnsH_rel_anchors (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3) :
    List.Forall₂ (eqnsH_Rel (d := d)) (d.anchors.map (eqnsH_anchorK (d := d)))
      ((ofCH d).anchors.map fun r => Eqn.zero r.b) := by
  change List.Forall₂ _ _ ((d.anchors.map fun p =>
    ({ gw := p.1, a := 0, b := p.2 } : Rec)).map fun r => Eqn.zero r.b)
  rw [List.map_map]
  refine forall₂_map_map fun r hr => ⟨?_, fun _ hb => ?_⟩
  · change (sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) r.2).1 =
      formOf (sqEdgesOf (ofCH d).tab r.2)
    rw [eqnsH_sqH_eq hw r.2]
  · change CFSG.KC.Ord.andB (Nat.blt r.2 d.nV)
      (Nat.beq (sqH (rowsG d.words) (rowsG d.tgt) (rowsG d.back) r.2).2 0) = true at hb
    rw [eqnsH_sqH_eq hw r.2, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hb
    have hany : (ofCH d).anchors.any (fun r' => r'.b == r.2) = true :=
      List.any_eq_true.2 ⟨_, List.mem_map_of_mem hr, by simp⟩
    change (decide (r.2 < d.nV) &&
      ((ofCH d).tab.walkEnd r.2 (posW ((ofCH d).tab.word r.2)) == 0) &&
      (ofCH d).anchors.any (fun r' => r'.b == r.2)) = true
    rw [hany, Bool.and_true]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact hb

private theorem eqnsH_rel (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3) :
    List.Forall₂ (eqnsH_Rel (d := d)) (eqnsH d (rowsG d.words) (rowsG d.tgt) (rowsG d.back))
      (ofCH d).eqns :=
  List.rel_append (List.rel_append (List.rel_append (eqnsH_rel_tree hw) (eqnsH_rel_trans hw))
    (eqnsH_rel_pairs hw)) (eqnsH_rel_anchors hw)

private theorem eqnsH_map_eq_of_forall₂ {α β γ : Type} {f : α → γ} {g : β → γ}
    {R : α → β → Prop} (hR : ∀ a b, R a b → f a = g b) {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : l₁.map f = l₂.map g := by
  induction h with
  | nil => rfl
  | cons h _ ih => rw [List.map_cons, List.map_cons, hR _ _ h, ih]

private theorem eqnsH_forall_of_forall₂ {α β : Type} {P : α → Prop} {Q : β → Prop}
    {R : α → β → Prop} (hR : ∀ a b, R a b → P a → Q b) {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (hP : ∀ a ∈ l₁, P a) : ∀ b ∈ l₂, Q b := by
  induction h with
  | nil => exact fun _ hb => absurd hb List.not_mem_nil
  | cons h _ ih =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hR _ _ h (hP _ List.mem_cons_self)
    · exact ih (fun a ha => hP a (List.mem_cons_of_mem _ ha)) b hb

theorem eqnsH_forms {d : CH} (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3) :
    (eqnsH d (rowsG d.words) (rowsG d.tgt) (rowsG d.back)).map Prod.snd = (ofCH d).forms :=
  eqnsH_map_eq_of_forall₂ (fun _ _ h => h.1) (eqnsH_rel hw)

theorem eqnsH_valid {d : CH} (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3) (hn : 0 < d.nV)
    (hv : ∀ q ∈ eqnsH d (rowsG d.words) (rowsG d.tgt) (rowsG d.back), q.1 = true) :
    (ofCH d).eqns.all (Eqn.valid (ofCH d)) = true :=
  List.all_eq_true.2 (eqnsH_forall_of_forall₂ (fun _ _ h hq => h.2 hn hq) (eqnsH_rel hw) hv)

theorem triH_geFinal {d : CH} (H : List (List Nat))
    (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 3)
    (hlen : CFSG.KC.LQT.Syl.lenK H = 3 * d.nV)
    (htri : triT (rowsG (List.map Prod.snd
      (eqnsH d (rowsG d.words) (rowsG d.tgt) (rowsG d.back)))) H = true)
    (hfs : ∀ f ∈ (ofCH d).forms, f < 2 ^ (3 * d.nV)) :
    geFinal (ofCH d) = true := by
  rw [geFinal, CFSG.Monster.B.Co2.allLt_iff]
  intro e he
  have hlen' : e < H.length := by
    rw [← CFSG.KC.LQT.Cov.Parse.lenK_length H, hlen]
    exact he
  obtain ⟨ks, hks⟩ := T.tri_pow _ H htri e hlen'
  rw [← hks, T.xorR_eq, eqnsH_forms hw]
  exact beq_iff_eq.2 (CFSG.KC.LQT.Cov.Ge.reduceF_gePivots_xor (M := 3 * d.nV)
    (fuel := 3 * d.nV + 5) hfs (by omega) ks)

private theorem eqnsH_flags_spec : ∀ Q : List (Bool × Nat),
    (List.rec (motive := fun _ => Bool) true (fun q _ ih => CFSG.KC.Ord.andB q.1 ih) Q : Bool) =
      true → ∀ q ∈ Q, q.1 = true
  | [], _, q, hq => absurd hq List.not_mem_nil
  | q :: Q, h, q', hq' => by
    change CFSG.KC.Ord.andB q.1 (List.rec (motive := fun _ => Bool) true
      (fun q _ ih => CFSG.KC.Ord.andB q.1 ih) Q) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact h.1
    · exact eqnsH_flags_spec Q h.2 q' hq'

theorem covHB_sound {cs : List Char} {D : CH} (hp : parseH cs = some D)
    (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) (hn : 0 < D.nV) {H : List (List Nat)}
    (h : covHB cs H = true) :
    (ofCH D).eqns.all (Eqn.valid (ofCH D)) = true ∧ geFinal (ofCH D) = true := by
  rw [covHB, hp] at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨hlenH, htri, hflagsH, hformsBound⟩ := h
  refine ⟨eqnsH_valid hw hn (eqnsH_flags_spec _ hflagsH),
    triH_geFinal H hw (Nat.beq_eq.mp hlenH) htri fun f hf => ?_⟩
  rw [← eqnsH_forms hw] at hf
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hf
  exact Nat.blt_eq.mp ((CFSG.KC.LQT.P.allL_iff _ _).1 hformsBound q.2 (List.mem_map_of_mem hq))

end CFSG.KC.LQT.Cov.H

end
