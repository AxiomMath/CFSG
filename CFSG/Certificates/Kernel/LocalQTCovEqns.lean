module

public import Certificates.Data.Kernel.LocalQT.Cov
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverCheck

public section

namespace CFSG.KC.LQT.Cov.Eqns

open CFSG.KC.LQT.Cov CFSG.QuasithinUnique.Ch1.M22Cover
open CFSG.QuasithinUnique.Ch1.TitsCover (formOf)

@[expose] def ofCD (D : CD) : CovData :=
  { xw0 := D.xw.getD 0 [], xw1 := D.xw.getD 1 [], xw2 := D.xw.getD 2 [], nV := D.nV,
    words := D.words.toArray, tgtA := D.tgt.toArray, backA := D.back.toArray, free := D.free,
    blocks := D.blocks.map fun b => { gw := b.1, va := b.2.1, vb := b.2.2.1, rhos := b.2.2.2 } }

theorem andB_eq (a b : Bool) : CFSG.KC.Ord.andB a b = (a && b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : CFSG.KC.Ord.notB a = !a := by cases a <;> rfl

theorem orB_eq (a b : Bool) : CFSG.KC.Ord.orB a b = (a || b) := by cases a <;> rfl

theorem letNN_eq (y : ℕ) (k : ℕ → ℕ × ℕ) : letNN y k = k y := by cases y <;> rfl

theorem getK_eq {α : Type} (l : List α) (i : ℕ) (d : α) :
    CFSG.KC.LQT.Syl.getK l i d = l.getD i d := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [List.getD_cons_succ]
      exact ih i

theorem lenK_eq {α : Type} (l : List α) : CFSG.KC.LQT.Syl.lenK l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg Nat.succ ih

theorem eqL_iff : ∀ (l m : List ℕ), CFSG.KC.LQT.Syl.eqL l m = true ↔ l = m
  | [], [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _ :: _ => by simp only [reduceCtorEq, iff_false]; exact Bool.false_ne_true
  | _ :: _, [] => by simp only [reduceCtorEq, iff_false]; exact Bool.false_ne_true
  | x :: t, y :: u => by
    change CFSG.KC.Ord.andB (Nat.beq x y) (CFSG.KC.LQT.Syl.eqL t u) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, Nat.beq_eq, eqL_iff t u, List.cons.injEq]

private theorem memL_iff (s : ℕ) (l : List ℕ) : CFSG.KC.LQT.S.memL s l = true ↔ s ∈ l := by
  induction l with
  | nil => simp only [List.not_mem_nil, iff_false]; exact Bool.false_ne_true
  | cons x l ih =>
    change CFSG.KC.Ord.orB (Nat.beq s x) (CFSG.KC.LQT.S.memL s l) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, Nat.beq_eq, ih, List.mem_cons]

theorem allBs_cons (b : Bool) (l : List Bool) :
    CFSG.KC.LQT.S.allBs (b :: l) = (b && CFSG.KC.LQT.S.allBs l) := andB_eq _ _

theorem allBs_nil : CFSG.KC.LQT.S.allBs [] = true := rfl

theorem allL_eq (l : List ℕ) (f : ℕ → Bool) : CFSG.KC.LQT.P.allL l f = l.all f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change CFSG.KC.Ord.andB (f x) (CFSG.KC.LQT.P.allL l f) = _
    rw [andB_eq, ih, List.all_cons]

theorem forall₂_map_map {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ} :
    ∀ {l : List α}, (∀ x ∈ l, R (f x) (g x)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => List.Forall₂.nil
  | x :: l, h => List.Forall₂.cons (h x List.mem_cons_self)
      (forall₂_map_map fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem toArray_getElem! {α : Type} [Inhabited α] (l : List α) (i : ℕ) :
    l.toArray[i]! = l.getD i default := by
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem getElem!_eq_getD {α : Type} [Inhabited α] (l : List α) (i : ℕ) :
    l[i]! = l.getD i default := by
  rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem map_val_map_fo (a : List ℕ) (ha : ∀ x ∈ a, x < 3) :
    (a.map fo).map Fin.val = a := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id a]
  exact List.map_congr_left fun x hx => Nat.mod_eq_of_lt (ha x hx)

variable {D : CD}

private theorem tab_word (D : CD) (v : ℕ) : (ofCD D).tab.word v = (D.words.getD v []).map fo := by
  show (D.words.toArray[v]!).map fo = _
  rw [toArray_getElem!]
  rfl

private theorem tab_tgt (D : CD) (v : ℕ) (i : Fin 3) :
    (ofCD D).tab.tgt v i = D.tgt.getD (3 * v + i) 0 := by
  show D.tgt.toArray[3 * v + (i : ℕ)]! = _
  rw [toArray_getElem!]
  rfl

private theorem tab_back (D : CD) (v : ℕ) (i : Fin 3) :
    (ofCD D).tab.back v i = D.back.getD (3 * v + i) 0 := by
  show D.back.toArray[3 * v + (i : ℕ)]! = _
  rw [toArray_getElem!]
  rfl

private theorem words_lt (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) (k : ℕ) :
    ∀ l ∈ D.words.getD k [], l < 3 := by
  intro l hl
  rw [List.getD_eq_getElem?_getD] at hl
  cases h : D.words[k]? with
  | none => simp [h] at hl
  | some w =>
    rw [h, Option.getD_some] at hl
    exact hw w (List.mem_of_getElem? h) l hl

private def cvL (l : ℕ × Bool) : Letter := (fo l.1, l.2)

private theorem fo_val_of_lt {i : ℕ} (hi : i < 3) : ((fo i : Fin 3) : ℕ) = i :=
  Nat.mod_eq_of_lt hi

private theorem step_eq (D : CD) (v : ℕ) (l : ℕ × Bool) (hl : l.1 < 3) :
    (ofCD D).tab.step v (cvL l) = stepK D v l := by
  obtain ⟨i, s⟩ := l
  have hfo := fo_val_of_lt (i := i) hl
  cases s
  · change (ofCD D).tab.back v (fo i) = CFSG.KC.LQT.Syl.getK D.back (3 * v + i) 0
    rw [tab_back, hfo, getK_eq]
  · change (ofCD D).tab.tgt v (fo i) = CFSG.KC.LQT.Syl.getK D.tgt (3 * v + i) 0
    rw [tab_tgt, hfo, getK_eq]

private theorem edge_eq (D : CD) (v : ℕ) (l : ℕ × Bool) (hl : l.1 < 3) :
    (ofCD D).tab.edge v (cvL l) = edgeK D v l := by
  obtain ⟨i, s⟩ := l
  have hfo := fo_val_of_lt (i := i) hl
  cases s
  · change 3 * (ofCD D).tab.back v (fo i) + (fo i : ℕ) =
      3 * CFSG.KC.LQT.Syl.getK D.back (3 * v + i) 0 + i
    rw [tab_back, hfo, getK_eq]
  · change 3 * v + (fo i : ℕ) = 3 * v + i
    rw [hfo]

private noncomputable def walkF (D : CD) (w : List (ℕ × Bool)) : ℕ → ℕ → ℕ × ℕ :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun f v => (f, v))
    (fun l _ ih f v => letNN (Nat.xor f (Nat.pow 2 (edgeK D v l))) fun f' =>
      letNN (stepK D v l) fun v' => ih f' v') w

private theorem walkF_eq (D : CD) :
    ∀ (w : List (ℕ × Bool)), (∀ l ∈ w, l.1 < 3) → ∀ f v : ℕ,
      walkF D w f v = (((ofCD D).tab.walkEdges v (w.map cvL)).foldl (fun f e => f ^^^ 2 ^ e) f,
        (ofCD D).tab.walkEnd v (w.map cvL))
  | [], _, _, _ => rfl
  | l :: w, hw, f, v => by
    have hl := hw l List.mem_cons_self
    have e : walkF D (l :: w) f v = walkF D w (f ^^^ 2 ^ edgeK D v l) (stepK D v l) := by
      change letNN _ (fun f' => letNN _ (fun v' => walkF D w f' v')) = _
      rw [letNN_eq, letNN_eq]
      rfl
    rw [e, walkF_eq D w (fun l' h => hw l' (List.mem_cons_of_mem _ h))]
    simp only [List.map_cons, CayTab.walkEdges, CayTab.walkEnd, List.foldl_cons, step_eq D v l hl,
      edge_eq D v l hl]

private theorem walkK_eq (D : CD) (v : ℕ) (w : List (ℕ × Bool)) (hw : ∀ l ∈ w, l.1 < 3) :
    walkK D v w = (formOf ((ofCD D).tab.walkEdges v (w.map cvL)),
      (ofCD D).tab.walkEnd v (w.map cvL)) :=
  walkF_eq D w hw 0 v

private theorem foldl_xor (es : List ℕ) (a : ℕ) :
    es.foldl (fun f e => f ^^^ 2 ^ e) a = a ^^^ formK es := by
  induction es generalizing a with
  | nil => exact (Nat.xor_zero a).symm
  | cons e es ih =>
    rw [List.foldl_cons, ih]
    change (a ^^^ 2 ^ e) ^^^ formK es = a ^^^ (2 ^ e ^^^ formK es)
    rw [Nat.xor_assoc]

private theorem formK_eq (es : List ℕ) : formK es = formOf es := by
  rw [formOf, foldl_xor, Nat.zero_xor]

private theorem map_posK (W : List ℕ) : (posK W).map cvL = posW (W.map fo) := by
  simp only [posK, posW, cvL, List.map_map, Function.comp_def]

private theorem map_invWK (W : List ℕ) : (invWK W).map cvL = invW (W.map fo) := by
  simp only [invWK, invW, cvL, List.map_map, Function.comp_def, List.map_reverse]

private theorem posK_lt {W : List ℕ} (hW : ∀ x ∈ W, x < 3) : ∀ l ∈ posK W, l.1 < 3 := by
  intro l hl
  unfold posK at hl
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
  exact hW x hx

private theorem invWK_lt {W : List ℕ} (hW : ∀ x ∈ W, x < 3) : ∀ l ∈ invWK W, l.1 < 3 := by
  intro l hl
  unfold invWK at hl
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
  exact hW x (List.mem_reverse.1 hx)

private theorem wordsK_lt (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) (k : ℕ) :
    ∀ l ∈ CFSG.KC.LQT.Syl.getK D.words k [], l < 3 := by
  rw [getK_eq]
  exact words_lt hw k

private theorem substK_lt (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) (vs : List ℕ)
    (ρ : List (ℕ × Bool)) : ∀ l ∈ substK D vs ρ, l.1 < 3 := by
  intro l hl
  unfold substK at hl
  obtain ⟨L, hL, hlL⟩ := List.mem_flatten.1 hl
  obtain ⟨⟨j, s⟩, -, rfl⟩ := List.mem_map.1 hL
  cases s
  · exact invWK_lt (wordsK_lt hw _) l hlL
  · exact posK_lt (wordsK_lt hw _) l hlL

private theorem map_substK (D : CD) (vs : List ℕ) (ρ : List (ℕ × Bool)) :
    (substK D vs ρ).map cvL = substW (ofCD D).tab (fun j => vs[j]!) ρ := by
  unfold substK substW
  rw [List.map_flatten, List.map_map, List.flatMap_def]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  obtain ⟨j, s⟩ := p
  simp only [Function.comp_apply, getElem!_eq_getD, tab_word, getK_eq]
  cases s
  · exact map_invWK _
  · exact map_posK _

private def cvE (p : ℕ × Fin 3) : ℕ × ℕ := (p.1, p.2)

private def edgesK (n : ℕ) : List (ℕ × ℕ) :=
  (List.map (fun v => List.map (fun i => (v, i)) [0, 1, 2]) (List.range n)).flatten

private def edgesN (n : ℕ) : List (ℕ × Fin 3) :=
  (List.range n).flatMap fun v => (List.finRange 3).map fun i => (v, i)

private theorem edgesK_eq (n : ℕ) : edgesK n = (edgesN n).map cvE := by
  unfold edgesK edgesN
  rw [List.map_flatMap, List.flatMap_def]
  congr 1

private noncomputable def isTK (D : CD) (p : ℕ × ℕ) : Bool :=
  CFSG.KC.LQT.Syl.eqL
    (CFSG.KC.LQT.Syl.getK D.words (CFSG.KC.LQT.Syl.getK D.tgt (3 * p.1 + p.2) 0) [])
    (CFSG.KC.LQT.Syl.getK D.words p.1 [] ++ [p.2])

private def isTN (D : CD) (p : ℕ × Fin 3) : Bool :=
  (ofCD D).tab.word ((ofCD D).tab.tgt p.1 p.2) == (ofCD D).tab.word p.1 ++ [p.2]

private theorem isTK_eq (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) (p : ℕ × Fin 3) :
    isTK D (cvE p) = isTN D p := by
  have hwk := words_lt hw
  rw [Bool.eq_iff_iff]
  unfold isTK isTN cvE
  simp only [eqL_iff, beq_iff_eq, tab_word, tab_tgt, getK_eq]
  have h3 : ([p.2] : List (Fin 3)) = [(p.2 : ℕ)].map fo := by simp [fo_val]
  have hlt : ∀ x ∈ D.words.getD p.1 [] ++ [(p.2 : ℕ)], x < 3 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hwk _ x hx
    · rw [List.mem_singleton.1 hx]
      exact p.2.2
  rw [h3, ← List.map_append]
  constructor
  · intro h
    rw [h]
  · intro h
    have := congrArg (List.map Fin.val) h
    rwa [map_val_map_fo _ (hwk _), map_val_map_fo _ hlt] at this

private def Rel (D : CD) (q : Bool × ℕ) (e : Eqn) : Prop :=
  q.2 = e.form (ofCD D) ∧ (0 < D.nV → q.1 = true → e.valid (ofCD D) = true)

private theorem rel_tree (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) :
    List.Forall₂ (Rel D)
      ((List.filter (isTK D) (edgesK D.nV)).map fun p =>
        (Nat.blt p.1 D.nV, Nat.pow 2 (3 * p.1 + p.2)))
      ((List.filter (isTN D) (edgesN D.nV)).map fun p => Eqn.tree p.1 p.2) := by
  have hf : List.filter (isTK D ∘ cvE) (edgesN D.nV) = List.filter (isTN D) (edgesN D.nV) :=
    List.filter_congr fun p _ => isTK_eq hw p
  rw [edgesK_eq, List.filter_map, hf, List.map_map]
  refine forall₂_map_map fun p hp => ⟨rfl, fun _ hb => ?_⟩
  have hT : isTN D p = true := (List.mem_filter.1 hp).2
  change (decide (p.1 < D.nV) && isTN D p) = true
  rw [hT, Bool.and_true, decide_eq_true_eq]
  exact Nat.blt_eq.mp hb

private noncomputable def wTK (D : CD) (p : ℕ × ℕ) : List (ℕ × Bool) :=
  posK (CFSG.KC.LQT.Syl.getK D.words p.1 []) ++ [(p.2, true)] ++
    invWK (CFSG.KC.LQT.Syl.getK D.words (CFSG.KC.LQT.Syl.getK D.tgt (3 * p.1 + p.2) 0) [])

private def wTN (D : CD) (p : ℕ × Fin 3) : List Letter :=
  posW ((ofCD D).tab.word p.1) ++ [(p.2, true)] ++
    invW ((ofCD D).tab.word ((ofCD D).tab.tgt p.1 p.2))

private theorem map_wTK (D : CD) (p : ℕ × Fin 3) : (wTK D (cvE p)).map cvL = wTN D p := by
  unfold wTK wTN cvE
  simp only [List.map_append, map_posK, map_invWK, tab_word, tab_tgt, getK_eq, List.map_cons,
    List.map_nil, cvL, fo_val]

private theorem wTK_lt (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) (p : ℕ × Fin 3) :
    ∀ l ∈ wTK D (cvE p), l.1 < 3 := by
  intro l hl
  unfold wTK at hl
  rcases List.mem_append.1 hl with hl | hl
  · rcases List.mem_append.1 hl with hl | hl
    · exact posK_lt (wordsK_lt hw _) l hl
    · rw [List.mem_singleton.1 hl]
      exact p.2.2
  · exact invWK_lt (wordsK_lt hw _) l hl

private noncomputable def transK (D : CD) (p : ℕ × ℕ) (j : ℕ) : Bool × ℕ :=
  (CFSG.KC.LQT.S.allBs [Nat.blt (CFSG.KC.LQT.Syl.getK D.tgt j 0) D.nV,
      Nat.beq (walkK D 0 (wTK D p)).2 0,
      Nat.beq (walkK D (CFSG.KC.LQT.Syl.getK D.tgt j 0) (wTK D p)).2
        (CFSG.KC.LQT.Syl.getK D.tgt j 0)],
    Nat.xor (walkK D 0 (wTK D p)).1 (walkK D (CFSG.KC.LQT.Syl.getK D.tgt j 0) (wTK D p)).1)

private theorem rel_trans (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) :
    List.Forall₂ (Rel D)
      ((List.filter (fun p => CFSG.KC.Ord.notB (isTK D p)) (edgesK D.nV)).map fun p =>
        [0, 1, 2].map (transK D p)).flatten
      ((List.filter (fun p => !isTN D p) (edgesN D.nV)).flatMap fun p =>
        (List.finRange 3).map fun j => Eqn.trans (wTN D p) 0 ((ofCD D).tab.tgt 0 j)) := by
  have hf : List.filter ((fun p => CFSG.KC.Ord.notB (isTK D p)) ∘ cvE) (edgesN D.nV) =
      List.filter (fun p => !isTN D p) (edgesN D.nV) :=
    List.filter_congr fun p _ => by rw [Function.comp_apply, notB_eq, isTK_eq hw p]
  rw [edgesK_eq, List.filter_map, hf, List.map_map, List.flatMap_def]
  refine List.rel_flatten (forall₂_map_map fun p _ => ?_)
  have h012 : ([0, 1, 2] : List ℕ) = (List.finRange 3).map Fin.val := rfl
  rw [Function.comp_apply, h012, List.map_map]
  refine forall₂_map_map fun j _ => ?_
  have hwl := wTK_lt hw p
  have h0 : (ofCD D).tab.tgt 0 j = CFSG.KC.LQT.Syl.getK D.tgt j 0 := by
    rw [tab_tgt, getK_eq, Nat.mul_zero, Nat.zero_add]
  refine ⟨?_, fun hn hb => ?_⟩
  · change Nat.xor (walkK D 0 (wTK D (cvE p))).1
        (walkK D (CFSG.KC.LQT.Syl.getK D.tgt j 0) (wTK D (cvE p))).1 =
      formOf ((ofCD D).tab.walkEdges 0 (wTN D p)) ^^^
        formOf ((ofCD D).tab.walkEdges ((ofCD D).tab.tgt 0 j) (wTN D p))
    rw [walkK_eq D _ _ hwl, walkK_eq D _ _ hwl, map_wTK, h0]
    rfl
  · change CFSG.KC.LQT.S.allBs [Nat.blt (CFSG.KC.LQT.Syl.getK D.tgt j 0) D.nV,
      Nat.beq (walkK D 0 (wTK D (cvE p))).2 0,
      Nat.beq (walkK D (CFSG.KC.LQT.Syl.getK D.tgt j 0) (wTK D (cvE p))).2
        (CFSG.KC.LQT.Syl.getK D.tgt j 0)] = true at hb
    rw [walkK_eq D _ _ hwl, walkK_eq D _ _ hwl, map_wTK, ← h0] at hb
    simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true, Nat.blt_eq,
      Nat.beq_eq] at hb
    change (decide (0 < D.nV) && decide ((ofCD D).tab.tgt 0 j < D.nV) &&
      ((ofCD D).tab.walkEnd 0 (wTN D p) == 0) &&
      ((ofCD D).tab.walkEnd ((ofCD D).tab.tgt 0 j) (wTN D p) == (ofCD D).tab.tgt 0 j)) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨hn, hb.1⟩, hb.2.1⟩, hb.2.2⟩

private def toBlk (b : List ℕ × List ℕ × List ℕ × List (List (ℕ × Bool))) : Blk :=
  { gw := b.1, va := b.2.1, vb := b.2.2.1, rhos := b.2.2.2 }

private theorem blocks_get (D : CD) (b : ℕ) :
    (ofCD D).blocks[b]! = toBlk (CFSG.KC.LQT.Syl.getK D.blocks b ([], [], [], [])) := by
  change (D.blocks.map toBlk)[b]! = _
  rw [getElem!_eq_getD, getK_eq]
  exact List.getD_map D.blocks (([] : List ℕ), ([] : List ℕ), ([] : List ℕ),
    ([] : List (List (ℕ × Bool)))) toBlk

private noncomputable def fusK (D : CD) (b : ℕ) (ρ : List (ℕ × Bool)) : Bool × ℕ :=
  (CFSG.KC.LQT.S.allBs [Nat.blt b (CFSG.KC.LQT.Syl.lenK D.blocks),
      CFSG.KC.LQT.P.allL (ρ.map fun p => p.1) (fun j =>
        Nat.blt j (CFSG.KC.LQT.Syl.lenK (CFSG.KC.LQT.Syl.getK D.blocks b ([], [], [], [])).2.1)),
      Nat.beq (walkK D 0
        (substK D (CFSG.KC.LQT.Syl.getK D.blocks b ([], [], [], [])).2.1 ρ)).2 0,
      Nat.beq (walkK D 0
        (substK D (CFSG.KC.LQT.Syl.getK D.blocks b ([], [], [], [])).2.2.1 ρ)).2 0],
    Nat.xor (Nat.xor
      (walkK D 0 (substK D (CFSG.KC.LQT.Syl.getK D.blocks b ([], [], [], [])).2.1 ρ)).1
      (walkK D 0 (substK D (CFSG.KC.LQT.Syl.getK D.blocks b ([], [], [], [])).2.2.1 ρ)).1)
      (formK (ρ.map fun p => 3 * D.nV + 32 * b + p.1)))

private theorem rel_fus (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) :
    List.Forall₂ (Rel D)
      ((List.range (CFSG.KC.LQT.Syl.lenK D.blocks)).map fun b =>
        (CFSG.KC.LQT.Syl.getK D.blocks b ([], [], [], [])).2.2.2.map (fusK D b)).flatten
      ((List.range (ofCD D).blocks.length).flatMap fun b =>
        ((ofCD D).blocks[b]!).rhos.map fun ρ => Eqn.fus b ρ) := by
  have hlen : (ofCD D).blocks.length = CFSG.KC.LQT.Syl.lenK D.blocks := by
    rw [lenK_eq]
    exact List.length_map _
  rw [hlen, List.flatMap_def]
  refine List.rel_flatten (forall₂_map_map fun b _ => ?_)
  rw [blocks_get]
  refine forall₂_map_map fun ρ _ => ?_
  set bl := CFSG.KC.LQT.Syl.getK D.blocks b ([], [], [], [])
  have hA := walkK_eq D 0 _ (substK_lt hw bl.2.1 ρ)
  have hB := walkK_eq D 0 _ (substK_lt hw bl.2.2.1 ρ)
  rw [map_substK] at hA hB
  unfold Rel
  simp only [Eqn.form, Eqn.valid, blocks_get]
  refine ⟨?_, fun _ hb => ?_⟩
  · change Nat.xor (Nat.xor (walkK D 0 (substK D bl.2.1 ρ)).1 (walkK D 0 (substK D bl.2.2.1 ρ)).1)
        (formK (ρ.map fun p => 3 * D.nV + 32 * b + p.1)) =
      formOf ((ofCD D).tab.walkEdges 0 (substW (ofCD D).tab (fun j => bl.2.1[j]!) ρ)) ^^^
        formOf ((ofCD D).tab.walkEdges 0 (substW (ofCD D).tab (fun j => bl.2.2.1[j]!) ρ)) ^^^
          formOf (ρ.map fun p => 3 * D.nV + 32 * b + p.1)
    rw [hA, hB, formK_eq]
    rfl
  · change CFSG.KC.LQT.S.allBs [Nat.blt b (CFSG.KC.LQT.Syl.lenK D.blocks),
      CFSG.KC.LQT.P.allL (ρ.map fun p => p.1) (fun j => Nat.blt j (CFSG.KC.LQT.Syl.lenK bl.2.1)),
      Nat.beq (walkK D 0 (substK D bl.2.1 ρ)).2 0,
      Nat.beq (walkK D 0 (substK D bl.2.2.1 ρ)).2 0] = true at hb
    rw [hA, hB] at hb
    simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
      allL_eq, List.all_map, List.all_eq_true, Function.comp_apply, lenK_eq] at hb
    change (decide (b < (ofCD D).blocks.length) &&
      ρ.all (fun p => decide (p.1 < bl.2.1.length)) &&
      ((ofCD D).tab.walkEnd 0 (substW (ofCD D).tab (fun j => bl.2.1[j]!) ρ) == 0) &&
      ((ofCD D).tab.walkEnd 0 (substW (ofCD D).tab (fun j => bl.2.2.1[j]!) ρ) == 0)) = true
    rw [hlen, lenK_eq]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true]
    exact ⟨⟨⟨hb.1, hb.2.1⟩, hb.2.2.1⟩, hb.2.2.2⟩

private theorem rel_free :
    List.Forall₂ (Rel D)
      (D.free.map fun e =>
        (CFSG.KC.Ord.andB (Nat.blt e (3 * D.nV)) (CFSG.KC.LQT.S.memL e D.free), Nat.pow 2 e))
      ((ofCD D).free.map Eqn.free) := by
  refine forall₂_map_map fun e _ => ⟨rfl, fun _ hb => ?_⟩
  rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, memL_iff] at hb
  change (decide (e < 3 * D.nV) && decide (e ∈ D.free)) = true
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact hb

private theorem eqnsK_rel (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) :
    List.Forall₂ (Rel D) (eqnsK D) (ofCD D).eqns :=
  List.rel_append (List.rel_append (List.rel_append (rel_tree hw) (rel_trans hw)) (rel_fus hw))
    rel_free

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

theorem eqnsK_forms {D : CD} (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) :
    (eqnsK D).map Prod.snd = (ofCD D).forms :=
  map_eq_of_forall₂ (fun _ _ h => h.1) (eqnsK_rel hw)

theorem eqnsK_valid {D : CD} (hw : ∀ w ∈ D.words, ∀ l ∈ w, l < 3) (hn : 0 < D.nV)
    (hv : ∀ q ∈ eqnsK D, q.1 = true) : (ofCD D).eqns.all (Eqn.valid (ofCD D)) = true :=
  List.all_eq_true.2 (forall_of_forall₂ (fun _ _ h hq => h.2 hn hq) (eqnsK_rel hw) hv)

theorem tab_word_ofCD (D : CD) (v : ℕ) : (ofCD D).tab.word v = (D.words.getD v []).map fo :=
  tab_word D v

theorem walkK_ofCD (D : CD) (v : ℕ) (w : List (ℕ × Bool)) (hw : ∀ l ∈ w, l.1 < 3) :
    walkK D v w = (formOf ((ofCD D).tab.walkEdges v (w.map fun l => (fo l.1, l.2))),
      (ofCD D).tab.walkEnd v (w.map fun l => (fo l.1, l.2))) :=
  walkK_eq D v w hw

end CFSG.KC.LQT.Cov.Eqns

end
