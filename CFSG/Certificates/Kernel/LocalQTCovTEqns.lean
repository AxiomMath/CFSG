module

public import CFSG.Certificates.Kernel.LocalQTCovTElts
public import CFSG.Certificates.Kernel.LocalQTCovEqns
public import CFSG.Certificates.Kernel.LocalQTCovPerm

public section

namespace CFSG.KC.LQT.Cov.TEqns

open CFSG.KC.LQT.Cov CFSG.KC.LQT.Cov.T CFSG.KC.LQT.Cov.Parse CFSG.KC.LQT.Cov.Eqns CFSG.KC.LQT.Syl
open CFSG.QuasithinUnique.Ch1.TitsCover

variable {d : CT}

private theorem tab_word (v : Nat) : (ofCT d).tab.word v = (d.words.getD v []).map fo := by
  show (d.words.toArray[v]!).map fo = _
  rw [CFSG.KC.LQT.Cov.T.toArray_getElem!_list]

private theorem tab_tgt (v : Nat) (i : Fin 2) :
    (ofCT d).tab.tgt v i = d.tgt.getD (2 * v + i) 0 := by
  show d.tgt.toArray[2 * v + (i : Nat)]! = _
  exact CFSG.KC.LQT.Cov.Perm.arr_get d.tgt (2 * v + i)

private theorem tab_back (v : Nat) (i : Fin 2) :
    (ofCT d).tab.back v i = d.back.getD (2 * v + i) 0 := by
  show d.back.toArray[2 * v + (i : Nat)]! = _
  exact CFSG.KC.LQT.Cov.Perm.arr_get d.back (2 * v + i)

private theorem words_lt (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 2) (k : Nat) :
    ∀ l ∈ d.words.getD k [], l < 2 := by
  intro l hl
  rw [List.getD_eq_getElem?_getD] at hl
  cases h : d.words[k]? with
  | none => simp [h] at hl
  | some w =>
    rw [h, Option.getD_some] at hl
    exact hw w (List.mem_of_getElem? h) l hl

private def cvL (l : Nat × Bool) : Letter := (fo l.1, l.2)

private theorem fo_val_of_lt {i : Nat} (hi : i < 2) : ((fo i : Fin 2) : Nat) = i :=
  Nat.mod_eq_of_lt hi

private theorem step_eq (v : Nat) (l : Nat × Bool) (hl : l.1 < 2) :
    (ofCT d).tab.step v (cvL l) = stepT (rowsG d.tgt) (rowsG d.back) v l := by
  obtain ⟨i, s⟩ := l
  have hfo := fo_val_of_lt (i := i) hl
  have hfoFin : (fo i : Fin 2) = ⟨i, hl⟩ := Fin.ext (by simpa using hfo)
  cases s
  · change (ofCT d).tab.back v (fo i) = getRG (rowsG d.back) (2 * v + i) 0
    rw [tab_back, getRG_rowsG, hfoFin]
  · change (ofCT d).tab.tgt v (fo i) = getRG (rowsG d.tgt) (2 * v + i) 0
    rw [tab_tgt, getRG_rowsG, hfoFin]

private theorem edge_eq (v : Nat) (l : Nat × Bool) (hl : l.1 < 2) :
    (ofCT d).tab.edge v (cvL l) = edgeT (rowsG d.back) v l := by
  obtain ⟨i, s⟩ := l
  have hfo := fo_val_of_lt (i := i) hl
  cases s
  · change 2 * (ofCT d).tab.back v (fo i) + (fo i : Nat) =
      2 * getRG (rowsG d.back) (2 * v + i) 0 + i
    rw [tab_back, getRG_rowsG, hfo]
  · change 2 * v + (fo i : Nat) = 2 * v + i
    rw [hfo]

private noncomputable def walkF (w : List (Nat × Bool)) : Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun f v => (f, v))
    (fun l _ ih f v => letNN (Nat.xor f (Nat.pow 2 (edgeT (rowsG d.back) v l))) fun f' =>
      letNN (stepT (rowsG d.tgt) (rowsG d.back) v l) fun v' => ih f' v') w

private theorem walkF_eq :
    ∀ (w : List (Nat × Bool)), (∀ l ∈ w, l.1 < 2) → ∀ f v : Nat,
      walkF (d := d) w f v = (((ofCT d).tab.walkEdges v (w.map cvL)).foldl
        (fun f e => f ^^^ 2 ^ e) f, (ofCT d).tab.walkEnd v (w.map cvL))
  | [], _, _, _ => rfl
  | l :: w, hw, f, v => by
    have hl := hw l List.mem_cons_self
    have e : walkF (d := d) (l :: w) f v =
        walkF (d := d) w (f ^^^ 2 ^ edgeT (rowsG d.back) v l)
          (stepT (rowsG d.tgt) (rowsG d.back) v l) := by
      change letNN _ (fun f' => letNN _ (fun v' => walkF (d := d) w f' v')) = _
      rw [letNN_eq, letNN_eq]
      rfl
    rw [e, walkF_eq w (fun l' h => hw l' (List.mem_cons_of_mem _ h))]
    simp only [List.map_cons, CayTab.walkEdges, CayTab.walkEnd, List.foldl_cons,
      step_eq v l hl, edge_eq v l hl]

private theorem walkT_eq (v : Nat) (w : List (Nat × Bool)) (hw : ∀ l ∈ w, l.1 < 2) :
    walkT (rowsG d.tgt) (rowsG d.back) v w =
      (formOf ((ofCT d).tab.walkEdges v (w.map cvL)),
        (ofCT d).tab.walkEnd v (w.map cvL)) :=
  walkF_eq w hw 0 v

private theorem foldl_xor (es : List Nat) (a : Nat) :
    es.foldl (fun f e => f ^^^ 2 ^ e) a = a ^^^ formK es := by
  induction es generalizing a with
  | nil => exact (Nat.xor_zero a).symm
  | cons e es ih =>
    rw [List.foldl_cons, ih]
    change (a ^^^ 2 ^ e) ^^^ formK es = a ^^^ (2 ^ e ^^^ formK es)
    rw [Nat.xor_assoc]

private theorem formK_eq (es : List Nat) : formK es = formOf es := by
  rw [formOf, foldl_xor, Nat.zero_xor]

private theorem map_posK (W : List Nat) : (posK W).map cvL = posW (W.map fo) := by
  simp only [posK, posW, cvL, List.map_map, Function.comp_def]

private theorem map_invWK (W : List Nat) : (invWK W).map cvL = invW (W.map fo) := by
  simp only [invWK, invW, cvL, List.map_map, Function.comp_def, List.map_reverse]

private theorem posK_lt {W : List Nat} (hW : ∀ x ∈ W, x < 2) : ∀ l ∈ posK W, l.1 < 2 := by
  intro l hl
  unfold posK at hl
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
  exact hW x hx

private theorem invWK_lt {W : List Nat} (hW : ∀ x ∈ W, x < 2) : ∀ l ∈ invWK W, l.1 < 2 := by
  intro l hl
  unfold invWK at hl
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
  exact hW x (List.mem_reverse.1 hx)

private theorem wordsK_lt (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 2) (k : Nat) :
    ∀ l ∈ getRG (rowsG d.words) k [], l < 2 := by
  rw [getRG_rowsG]
  exact words_lt hw k

private theorem substT_lt (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 2) (vs : List Nat)
    (ρ : List (Nat × Bool)) : ∀ l ∈ substT (rowsG d.words) vs ρ, l.1 < 2 := by
  intro l hl
  unfold substT at hl
  obtain ⟨L, hL, hlL⟩ := List.mem_flatten.1 hl
  obtain ⟨⟨j, s⟩, -, rfl⟩ := List.mem_map.1 hL
  cases s
  · exact invWK_lt (wordsK_lt hw _) l hlL
  · exact posK_lt (wordsK_lt hw _) l hlL

private theorem map_substT (vs : List Nat) (ρ : List (Nat × Bool)) :
    (substT (rowsG d.words) vs ρ).map cvL = substW (ofCT d).tab (fun j => vs[j]!) ρ := by
  unfold substT substW
  rw [List.map_flatten, List.map_map, List.flatMap_def]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  obtain ⟨j, s⟩ := p
  simp only [Function.comp_apply, getElem!_eq_getD, tab_word, getRG_rowsG, getK_getD]
  cases s
  · exact map_invWK _
  · exact map_posK _

private theorem map_val_map_fo (a : List Nat) (ha : ∀ x ∈ a, x < 2) :
    (a.map fo).map Fin.val = a := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id a]
  exact List.map_congr_left fun x hx => Nat.mod_eq_of_lt (ha x hx)

private def cvE (p : Nat × Fin 2) : Nat × Nat := (p.1, p.2)

private def edgesK (n : Nat) : List (Nat × Nat) :=
  (List.map (fun v => List.map (fun i => (v, i)) [0, 1]) (List.range n)).flatten

private def edgesN (n : Nat) : List (Nat × Fin 2) :=
  (List.range n).flatMap fun v => (List.finRange 2).map fun i => (v, i)

private theorem edgesK_eq (n : Nat) : edgesK n = (edgesN n).map cvE := by
  unfold edgesK edgesN
  rw [List.map_flatMap, List.flatMap_def]
  congr 1

private noncomputable def isTK (p : Nat × Nat) : Bool :=
  CFSG.KC.LQT.Syl.eqL (getRG (rowsG d.words) (getRG (rowsG d.tgt) (2 * p.1 + p.2) 0) [])
    (getRG (rowsG d.words) p.1 [] ++ [p.2])

private def isTN (p : Nat × Fin 2) : Bool :=
  (ofCT d).tab.word ((ofCT d).tab.tgt p.1 p.2) == ((ofCT d).tab.word p.1 ++ [p.2])

private theorem isTK_eq (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 2) (p : Nat × Fin 2) :
    isTK (d := d) (cvE p) = isTN (d := d) p := by
  have hwk := words_lt hw p.1
  rw [Bool.eq_iff_iff]
  unfold isTK isTN cvE
  simp only [eqL_iff, beq_iff_eq, tab_word, tab_tgt, getRG_rowsG, getK_getD]
  have h3 : ([p.2] : List (Fin 2)) = [(p.2 : Nat)].map fo := by simp [fo_val]
  have hlt : ∀ x ∈ d.words.getD p.1 [] ++ [(p.2 : Nat)], x < 2 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hwk x hx
    · rw [List.mem_singleton.1 hx]
      exact p.2.2
  rw [h3, ← List.map_append]
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg (List.map Fin.val) h
    have hwk' := words_lt hw (d.tgt.getD (2 * p.1 + p.2) 0)
    rwa [map_val_map_fo _ hwk', map_val_map_fo _ hlt] at this

private def Rel (q : Bool × Nat) (e : Eqn) : Prop :=
  q.2 = e.form (ofCT d) ∧ (0 < d.nV → q.1 = true → e.valid (ofCT d) = true)

private theorem rel_tree (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 2) :
    List.Forall₂ (Rel (d := d))
      ((List.filter (isTK (d := d)) (edgesK d.nV)).map fun p =>
        (Nat.blt p.1 d.nV, Nat.pow 2 (2 * p.1 + p.2)))
      ((List.filter (isTN (d := d)) (edgesN d.nV)).map fun p => Eqn.tree p.1 p.2) := by
  have hf : List.filter (isTK (d := d) ∘ cvE) (edgesN d.nV) =
      List.filter (isTN (d := d)) (edgesN d.nV) :=
    List.filter_congr fun p _ => isTK_eq hw p
  rw [edgesK_eq, List.filter_map, hf, List.map_map]
  refine forall₂_map_map fun p hp => ⟨rfl, fun _ hb => ?_⟩
  have hT : isTN (d := d) p = true := (List.mem_filter.1 hp).2
  change (decide (p.1 < d.nV) && isTN (d := d) p) = true
  rw [hT, Bool.and_true, decide_eq_true_eq]
  exact Nat.blt_eq.mp hb

private noncomputable def wTK (p : Nat × Nat) : List (Nat × Bool) :=
  posK (getRG (rowsG d.words) p.1 []) ++ [(p.2, true)] ++
    invWK (getRG (rowsG d.words) (getRG (rowsG d.tgt) (2 * p.1 + p.2) 0) [])

private def wTN (p : Nat × Fin 2) : List Letter :=
  posW ((ofCT d).tab.word p.1) ++ [(p.2, true)] ++
    invW ((ofCT d).tab.word ((ofCT d).tab.tgt p.1 p.2))

private theorem map_wTK (p : Nat × Fin 2) : (wTK (d := d) (cvE p)).map cvL = wTN (d := d) p := by
  unfold wTK wTN cvE
  simp only [List.map_append, map_posK, map_invWK, tab_word, tab_tgt, getRG_rowsG, getK_getD,
    List.map_cons, List.map_nil, cvL, fo_val]

private theorem wTK_lt (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 2) (p : Nat × Fin 2) :
    ∀ l ∈ wTK (d := d) (cvE p), l.1 < 2 := by
  intro l hl
  unfold wTK at hl
  rcases List.mem_append.1 hl with hl | hl
  · rcases List.mem_append.1 hl with hl | hl
    · exact posK_lt (wordsK_lt hw _) l hl
    · rw [List.mem_singleton.1 hl]
      exact p.2.2
  · exact invWK_lt (wordsK_lt hw _) l hl

private noncomputable def transK (p : Nat × Nat) (j : Nat) : Bool × Nat :=
  (CFSG.KC.LQT.S.allBs [Nat.blt (getRG (rowsG d.tgt) j 0) d.nV,
      Nat.beq (walkT (rowsG d.tgt) (rowsG d.back) 0 (wTK (d := d) p)).2 0,
      Nat.beq (walkT (rowsG d.tgt) (rowsG d.back) (getRG (rowsG d.tgt) j 0)
        (wTK (d := d) p)).2 (getRG (rowsG d.tgt) j 0)],
    Nat.xor (walkT (rowsG d.tgt) (rowsG d.back) 0 (wTK (d := d) p)).1
      (walkT (rowsG d.tgt) (rowsG d.back) (getRG (rowsG d.tgt) j 0) (wTK (d := d) p)).1)

private theorem rel_trans (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 2) :
    List.Forall₂ (Rel (d := d))
      ((List.filter (fun p => CFSG.KC.Ord.notB (isTK (d := d) p)) (edgesK d.nV)).map fun p =>
        [0, 1].map (transK (d := d) p)).flatten
      ((List.filter (fun p => !isTN (d := d) p) (edgesN d.nV)).flatMap fun p =>
        (List.finRange 2).map fun j => Eqn.trans (wTN (d := d) p) 0 ((ofCT d).tab.tgt 0 j)) := by
  have hf : List.filter ((fun p => CFSG.KC.Ord.notB (isTK (d := d) p)) ∘ cvE) (edgesN d.nV) =
      List.filter (fun p => !isTN (d := d) p) (edgesN d.nV) :=
    List.filter_congr fun p _ => by
      rw [Function.comp_apply, CFSG.KC.LQT.Cov.Parse.notB_eq', isTK_eq hw p]
  rw [edgesK_eq, List.filter_map, hf, List.map_map, List.flatMap_def]
  refine List.rel_flatten (forall₂_map_map fun p _ => ?_)
  have h012 : ([0, 1] : List Nat) = (List.finRange 2).map Fin.val := rfl
  rw [Function.comp_apply, h012, List.map_map]
  refine forall₂_map_map fun j _ => ?_
  have hwl := wTK_lt hw p
  have h0 : (ofCT d).tab.tgt 0 j = getRG (rowsG d.tgt) j 0 := by
    simp [tab_tgt, getRG_rowsG]
  refine ⟨?_, fun hn hb => ?_⟩
  · change Nat.xor (walkT (rowsG d.tgt) (rowsG d.back) 0 (wTK (d := d) (cvE p))).1
        (walkT (rowsG d.tgt) (rowsG d.back) (getRG (rowsG d.tgt) j 0)
          (wTK (d := d) (cvE p))).1 =
      formOf ((ofCT d).tab.walkEdges 0 (wTN (d := d) p)) ^^^
        formOf ((ofCT d).tab.walkEdges ((ofCT d).tab.tgt 0 j) (wTN (d := d) p))
    rw [walkT_eq (d := d) _ _ hwl, walkT_eq (d := d) _ _ hwl, map_wTK, h0]
    rfl
  · change CFSG.KC.LQT.S.allBs [Nat.blt (getRG (rowsG d.tgt) j 0) d.nV,
      Nat.beq (walkT (rowsG d.tgt) (rowsG d.back) 0 (wTK (d := d) (cvE p))).2 0,
      Nat.beq (walkT (rowsG d.tgt) (rowsG d.back) (getRG (rowsG d.tgt) j 0)
        (wTK (d := d) (cvE p))).2 (getRG (rowsG d.tgt) j 0)] = true at hb
    rw [walkT_eq (d := d) _ _ hwl, walkT_eq (d := d) _ _ hwl, map_wTK, ← h0] at hb
    simp only [allBs_cons, allBs_nil, Bool.and_true,
      Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hb
    change (decide (0 < d.nV) && decide ((ofCT d).tab.tgt 0 j < d.nV) &&
      ((ofCT d).tab.walkEnd 0 (wTN (d := d) p) == 0) &&
      ((ofCT d).tab.walkEnd ((ofCT d).tab.tgt 0 j) (wTN (d := d) p) == (ofCT d).tab.tgt 0 j)) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨hn, hb.1⟩, hb.2.1⟩, hb.2.2⟩

private def toBlk (b : List Int × List Nat × List Nat × List (List (Nat × Bool))) : Blk :=
  { gw := b.1, va := b.2.1, vb := b.2.2.1, rhos := b.2.2.2 }

private theorem blocks_get (b : Nat) :
    (ofCT d).blocks[b]! = toBlk (getK d.blocks b ([], [], [], [])) := by
  change (d.blocks.map toBlk)[b]! = _
  rw [getElem!_eq_getD, getK_getD]
  exact List.getD_map d.blocks (([] : List Int), ([] : List Nat), ([] : List Nat),
    ([] : List (List (Nat × Bool)))) toBlk

private noncomputable def fusK (b : Nat) (ρ : List (Nat × Bool)) : Bool × Nat :=
  (CFSG.KC.LQT.S.allBs [Nat.blt b (CFSG.KC.LQT.Syl.lenK d.blocks),
      CFSG.KC.LQT.P.allL (ρ.map fun p => p.1) (fun j =>
        Nat.blt j (CFSG.KC.LQT.Syl.lenK (getK d.blocks b ([], [], [], [])).2.1)),
      Nat.beq (walkT (rowsG d.tgt) (rowsG d.back) 0
        (substT (rowsG d.words) (getK d.blocks b ([], [], [], [])).2.1 ρ)).2 0,
      Nat.beq (walkT (rowsG d.tgt) (rowsG d.back) 0
        (substT (rowsG d.words) (getK d.blocks b ([], [], [], [])).2.2.1 ρ)).2 0],
    Nat.xor (Nat.xor
      (walkT (rowsG d.tgt) (rowsG d.back) 0
        (substT (rowsG d.words) (getK d.blocks b ([], [], [], [])).2.1 ρ)).1
      (walkT (rowsG d.tgt) (rowsG d.back) 0
        (substT (rowsG d.words) (getK d.blocks b ([], [], [], [])).2.2.1 ρ)).1)
      (formK (ρ.map fun p => 2 * d.nV + 32 * b + p.1)))

private theorem rel_fus (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 2) :
    List.Forall₂ (Rel (d := d))
      ((List.range (CFSG.KC.LQT.Syl.lenK d.blocks)).map fun b =>
        (getK d.blocks b ([], [], [], [])).2.2.2.map (fusK (d := d) b)).flatten
      ((List.range (ofCT d).blocks.length).flatMap fun b =>
        ((ofCT d).blocks[b]!).rhos.map fun ρ => Eqn.fus b ρ) := by
  have hlen : (ofCT d).blocks.length = CFSG.KC.LQT.Syl.lenK d.blocks := by
    rw [CFSG.KC.LQT.Cov.Perm.slenK_eq]
    exact List.length_map _
  rw [hlen, List.flatMap_def]
  refine List.rel_flatten (forall₂_map_map fun b _ => ?_)
  rw [blocks_get]
  refine forall₂_map_map fun ρ _ => ?_
  set bl := getK d.blocks b ([], [], [], [])
  have hA := walkT_eq (d := d) 0 _ (substT_lt hw bl.2.1 ρ)
  have hB := walkT_eq (d := d) 0 _ (substT_lt hw bl.2.2.1 ρ)
  rw [map_substT] at hA hB
  unfold Rel
  simp only [Eqn.form, Eqn.valid, blocks_get]
  refine ⟨?_, fun _ hb => ?_⟩
  · change Nat.xor (Nat.xor
        (walkT (rowsG d.tgt) (rowsG d.back) 0 (substT (rowsG d.words) bl.2.1 ρ)).1
        (walkT (rowsG d.tgt) (rowsG d.back) 0 (substT (rowsG d.words) bl.2.2.1 ρ)).1)
        (formK (ρ.map fun p => 2 * d.nV + 32 * b + p.1)) =
      formOf ((ofCT d).tab.walkEdges 0 (substW (ofCT d).tab (fun j => bl.2.1[j]!) ρ)) ^^^
        formOf ((ofCT d).tab.walkEdges 0 (substW (ofCT d).tab (fun j => bl.2.2.1[j]!) ρ)) ^^^
          formOf (ρ.map fun p => 2 * d.nV + 32 * b + p.1)
    rw [hA, hB, formK_eq]
    rfl
  · change CFSG.KC.LQT.S.allBs [Nat.blt b (CFSG.KC.LQT.Syl.lenK d.blocks),
      CFSG.KC.LQT.P.allL (ρ.map fun p => p.1) (fun j =>
        Nat.blt j (CFSG.KC.LQT.Syl.lenK bl.2.1)),
      Nat.beq (walkT (rowsG d.tgt) (rowsG d.back) 0 (substT (rowsG d.words) bl.2.1 ρ)).2 0,
      Nat.beq (walkT (rowsG d.tgt) (rowsG d.back) 0 (substT (rowsG d.words) bl.2.2.1 ρ)).2 0] = true at hb
    rw [hA, hB] at hb
    simp only [allBs_cons, allBs_nil, Bool.and_true,
      Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, allL_eq,
      List.all_map, List.all_eq_true, Function.comp_apply, CFSG.KC.LQT.Cov.Perm.slenK_eq] at hb
    change (decide (b < (ofCT d).blocks.length) &&
      ρ.all (fun p => decide (p.1 < bl.2.1.length)) &&
      ((ofCT d).tab.walkEnd 0 (substW (ofCT d).tab (fun j => bl.2.1[j]!) ρ) == 0) &&
      ((ofCT d).tab.walkEnd 0 (substW (ofCT d).tab (fun j => bl.2.2.1[j]!) ρ) == 0)) = true
    rw [hlen, CFSG.KC.LQT.Cov.Perm.slenK_eq]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true]
    exact ⟨⟨⟨hb.1, hb.2.1⟩, hb.2.2.1⟩, hb.2.2.2⟩

private theorem eqnsT_rel (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 2) :
    List.Forall₂ (Rel (d := d)) (eqnsT d (rowsG d.words) (rowsG d.tgt) (rowsG d.back))
      (ofCT d).eqns :=
  List.rel_append (List.rel_append (rel_tree hw) (rel_trans hw)) (rel_fus hw)

private theorem map_eq_of_forall₂ {α β γ : Type} {f : α → γ} {g : β → γ} {R : α → β → Prop}
    (hR : ∀ a b, R a b → f a = g b) {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    l₁.map f = l₂.map g := by
  induction h with
  | nil => rfl
  | cons h _ ih => rw [List.map_cons, List.map_cons, hR _ _ h, ih]

private theorem forall_of_forall₂ {α β : Type} {P : α → Prop} {Q : β → Prop}
    {R : α → β → Prop} (hR : ∀ a b, R a b → P a → Q b) {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (hP : ∀ a ∈ l₁, P a) : ∀ b ∈ l₂, Q b := by
  induction h with
  | nil => exact fun _ hb => absurd hb List.not_mem_nil
  | cons h _ ih =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hR _ _ h (hP _ List.mem_cons_self)
    · exact ih (fun a ha => hP a (List.mem_cons_of_mem _ ha)) b hb

theorem eqnsT_forms {d : CT} (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 2) :
    (eqnsT d (rowsG d.words) (rowsG d.tgt) (rowsG d.back)).map Prod.snd = (ofCT d).forms :=
  map_eq_of_forall₂ (fun _ _ h => h.1) (eqnsT_rel hw)

theorem eqnsT_valid {d : CT} (hw : ∀ w ∈ d.words, ∀ l ∈ w, l < 2) (hn : 0 < d.nV)
    (hv : ∀ q ∈ eqnsT d (rowsG d.words) (rowsG d.tgt) (rowsG d.back), q.1 = true) :
    (ofCT d).eqns.all (Eqn.valid (ofCT d)) = true :=
  List.all_eq_true.2 (forall_of_forall₂ (fun _ _ h hq => h.2 hn hq) (eqnsT_rel hw) hv)

end CFSG.KC.LQT.Cov.TEqns

end
