module

public import CFSG.Certificates.Kernel.LocalQTTab2ParseSound
public import CFSG.Certificates.Kernel.LocalQTSmallSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux

public section

namespace CFSG.KC.LQT.T2

open Equiv CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.QuasithinUnique.Unc25G2
  CFSG.QuasithinUnique.Unc25G2.M2x CFSG.QuasithinUnique.Unc25G2.Tbl

open CFSG.KC.Ord hiding tbl

theorem getDK_eq : ∀ (l : List ℕ) (i d : ℕ), getDK l i d = l.getD i d
  | [], i, d => by simp [getDK]
  | x :: l, 0, d => rfl
  | x :: l, i + 1, d => by
    change getDK l (i + 1 - 1) d = _
    rw [Nat.add_sub_cancel, getDK_eq l i d]
    simp

theorem headK_eq (l : List ℕ) (d : ℕ) : headK l d = l.headD d := by
  cases l <;> rfl

theorem letL_eq (y : ℕ) (k : ℕ → List ℕ) : letL y k = k y := by
  cases y <;> rfl

theorem normQ_spec (F R : List ℕ) (k : List ℕ → List ℕ → List ℕ) :
    ∃ F' R', normQ F R k = k F' R' ∧ F' ++ R'.reverse = F ++ R.reverse ∧ (F' = [] → R' = []) := by
  cases F with
  | nil => exact ⟨R.reverse, [], rfl, by simp, fun _ => rfl⟩
  | cons x xs => exact ⟨x :: xs, R, rfl, rfl, fun h => absurd h (List.cons_ne_nil _ _)⟩

theorem dropQ_spec (k : List ℕ → List ℕ → List ℕ) : ∀ (m : ℕ) (F R : List ℕ),
    ∃ F' R', dropQ m k F R = k F' R' ∧ F' ++ R'.reverse = (F ++ R.reverse).drop m ∧
      (F' = [] → R' = [])
  | 0, F, R => by
    obtain ⟨F', R', e, h1, h2⟩ := normQ_spec F R k
    exact ⟨F', R', e, by rw [List.drop_zero]; exact h1, h2⟩
  | m + 1, F, R => by
    obtain ⟨F₁, R₁, e, h1, h2⟩ := normQ_spec F R (fun F₁ R₁ => dropQ m k (List.tail F₁) R₁)
    obtain ⟨F', R', e', h1', h2'⟩ := dropQ_spec k m F₁.tail R₁
    refine ⟨F', R', ?_, ?_, h2'⟩
    · change normQ F R (fun F₁ R₁ => dropQ m k (List.tail F₁) R₁) = _
      rw [e]
      exact e'
    · rw [h1', ← h1]
      cases F₁ with
      | nil => simp [h2 rfl]
      | cons x xs => rfl

theorem headD_queue {F R Q : List ℕ} (h : F ++ R.reverse = Q) (hF : F = [] → R = []) (d : ℕ) :
    F.headD d = Q.headD d := by
  cases F with
  | nil =>
    rw [hF rfl] at h
    rw [← h]
    rfl
  | cons x xs =>
    rw [← h]
    rfl

theorem headD_drop (l : List ℕ) (i d : ℕ) : (l.drop i).headD d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, ← List.head?_drop]
  cases l.drop i <;> rfl

@[expose] def bfsG {α : Type} (op : α → α → α) (d : α) (gens : List α) (start : α)
    (par : List (ℕ × ℕ)) : List α :=
  par.foldl (fun acc pk => acc ++ [op (acc.getD pk.1 start) (gens.getD pk.2 d)]) [start]

theorem bfs_eq_bfsG (op : List ℕ → List ℕ → List ℕ) (d : List ℕ) (gens : List (List ℕ))
    (start : List ℕ) (par : List (ℕ × ℕ)) : bfs op d gens start par = bfsG op d gens start par :=
  rfl

theorem foldl_map_bfs {α β : Type} (f : α → β) (opα : α → α → α) (opβ : β → β → β)
    (hop : ∀ x g, f (opα x g) = opβ (f x) (f g)) (dα : α) (gα : List α) (sα : α) :
    ∀ (par : List (ℕ × ℕ)) (acc : List α),
      (par.foldl (fun acc pk => acc ++ [opα (acc.getD pk.1 sα) (gα.getD pk.2 dα)]) acc).map f =
        par.foldl (fun acc pk => acc ++ [opβ (acc.getD pk.1 (f sα)) ((gα.map f).getD pk.2 (f dα))])
          (acc.map f)
  | [], _ => rfl
  | pk :: par, acc => by
    rw [List.foldl_cons, List.foldl_cons, foldl_map_bfs f opα opβ hop dα gα sα par, List.map_append,
      List.map_singleton, hop, List.getD_map, List.getD_map]

theorem bfsG_map {α β : Type} (f : α → β) (opα : α → α → α) (opβ : β → β → β)
    (hop : ∀ x g, f (opα x g) = opβ (f x) (f g)) (dα : α) (gα : List α) (sα : α)
    (par : List (ℕ × ℕ)) :
    (bfsG opα dα gα sα par).map f = bfsG opβ (f dα) (gα.map f) (f sα) par :=
  foldl_map_bfs f opα opβ hop dα gα sα par [sα]

@[expose] noncomputable def goQ (op : ℕ → ℕ → ℕ) (d : ℕ) (gens : List ℕ) (start : ℕ)
    (par : List (ℕ × ℕ)) : List ℕ → ℕ → List ℕ → List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ → ℕ → List ℕ → List ℕ → List ℕ)
    (fun _ _ _ O => O)
    (fun pk _ ih F c R O => dropQ (Nat.sub pk.1 c) (fun F₁ R₁ =>
      letL (op (headK F₁ start) (getDK gens pk.2 d)) fun y =>
        ih F₁ pk.1 (List.cons y R₁) (List.cons y O)) F R) par

@[expose] noncomputable def monoA (par : List (ℕ × ℕ)) : ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun pk _ ih i c => letB i fun i' => andB (Nat.ble c pk.1) (andB (Nat.ble pk.1 i')
      (ih (Nat.succ i') pk.1))) par

theorem goQ_spec (op : ℕ → ℕ → ℕ) (d : ℕ) (gens : List ℕ) (start : ℕ) :
    ∀ (par : List (ℕ × ℕ)) (acc : List ℕ) (i c : ℕ) (F R : List ℕ), monoA par i c = true →
      acc.length = i + 1 → c ≤ acc.length → F ++ R.reverse = acc.drop c →
      goQ op d gens start par F c R acc.reverse =
        (par.foldl (fun acc pk => acc ++ [op (acc.getD pk.1 start) (gens.getD pk.2 d)])
          acc).reverse
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | pk :: par, acc, i, c, F, R, hm, hl, hc, hq => by
    have hm' : andB (Nat.ble c pk.1) (andB (Nat.ble pk.1 i) (monoA par (i + 1) pk.1)) = true := by
      rw [← letB_eq i (fun i' => andB (Nat.ble c pk.1) (andB (Nat.ble pk.1 i')
        (monoA par (i' + 1) pk.1)))]
      exact hm
    rw [andB_iff, andB_iff, Nat.ble_eq, Nat.ble_eq] at hm'
    obtain ⟨h1, h2, h3⟩ := hm'
    obtain ⟨F', R', e, hq', hF'⟩ := dropQ_spec (fun F₁ R₁ =>
      letL (op (headK F₁ start) (getDK gens pk.2 d)) fun y =>
        goQ op d gens start par F₁ pk.1 (y :: R₁) (y :: acc.reverse)) (pk.1 - c) F R
    have hu : goQ op d gens start (pk :: par) F c R acc.reverse = dropQ (pk.1 - c) (fun F₁ R₁ =>
      letL (op (headK F₁ start) (getDK gens pk.2 d)) fun y =>
        goQ op d gens start par F₁ pk.1 (y :: R₁) (y :: acc.reverse)) F R := rfl
    have hdrop : F' ++ R'.reverse = acc.drop pk.1 := by
      rw [hq', hq, List.drop_drop]
      congr 1
      omega
    rw [hu, e, letL_eq, headK_eq, headD_queue hdrop hF', headD_drop, getDK_eq, List.foldl_cons]
    have key := goQ_spec op d gens start par
      (acc ++ [op (acc.getD pk.1 start) (gens.getD pk.2 d)]) (i + 1) pk.1 F'
      (op (acc.getD pk.1 start) (gens.getD pk.2 d) :: R') h3 (by simp [hl]) (by simp; omega)
      (by rw [List.reverse_cons, ← List.append_assoc, hdrop,
        List.drop_append_of_le_length (by omega)])
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at key
    exact key

theorem bfsQ_eq (op : ℕ → ℕ → ℕ) (d : ℕ) (gens : List ℕ) (start : ℕ) (par : List (ℕ × ℕ))
    (hm : monoK par = true) : bfsQ op d gens start par = bfsG op d gens start par := by
  have e : bfsQ op d gens start par = (goQ op d gens start par [start] 0 [] [start]).reverse := rfl
  have key := goQ_spec op d gens start par [start] 0 0 [start] [] hm rfl (by simp) (by simp)
  rw [List.reverse_singleton] at key
  rw [e, key, List.reverse_reverse]
  rfl

theorem spanLt_permT (x : ℕ) (k : List ℕ → List ℕ → List ℕ) : ∀ (ys acc : List ℕ),
    ∃ p r, spanLt x ys k acc = k p r ∧ (p ++ r).Perm (acc ++ ys)
  | [], acc => ⟨acc.reverse, [], rfl, by
      rw [List.append_nil, List.append_nil]
      exact List.reverse_perm acc⟩
  | y :: ys', acc => by
    change ∃ p r, Bool.rec (motive := fun _ => List ℕ) (k (List.reverse acc) (List.cons y ys'))
      (spanLt x ys' k (List.cons y acc)) (Nat.blt y x) = k p r ∧ (p ++ r).Perm (acc ++ y :: ys')
    cases Nat.blt y x
    · exact ⟨acc.reverse, y :: ys', rfl, (List.reverse_perm acc).append_right _⟩
    · obtain ⟨p, r, e, hp⟩ := spanLt_permT x k ys' (y :: acc)
      exact ⟨p, r, e, hp.trans List.perm_middle.symm⟩

theorem mergeK_permT : ∀ (xs ys : List ℕ), (mergeK xs ys).Perm (xs ++ ys)
  | [], ys => List.Perm.refl ys
  | x :: xs, ys => by
    change (spanLt x ys (fun p r => List.append p (List.cons x (mergeK xs r))) []).Perm _
    obtain ⟨p, r, e, hp⟩ :=
      spanLt_permT x (fun p r => List.append p (List.cons x (mergeK xs r))) ys []
    rw [e]
    rw [List.nil_append] at hp
    change (p ++ x :: mergeK xs r).Perm (x :: (xs ++ ys))
    refine (((mergeK_permT xs r).cons x).append_left p).trans (List.perm_middle.trans ?_)
    refine List.Perm.cons x ?_
    rw [← List.append_assoc]
    exact (List.perm_append_comm.append_right r).trans
      (by rw [List.append_assoc]; exact hp.append_left xs)

@[expose] noncomputable def passGoT (rs : List (List ℕ)) (o : Option (List ℕ)) : List (List ℕ) :=
  List.rec (motive := fun _ => Option (List ℕ) → List (List ℕ))
    (fun o => Option.rec (motive := fun _ => List (List ℕ)) [] (fun a => [a]) o)
    (fun r _ ih o => Option.rec (motive := fun _ => List (List ℕ)) (ih (some r))
      (fun a => List.cons (mergeK a r) (ih none)) o) rs o

theorem passGoT_perm : ∀ (rs : List (List ℕ)) (o : Option (List ℕ)),
    (passGoT rs o).flatten.Perm (o.getD [] ++ rs.flatten)
  | [], none => List.Perm.refl _
  | [], some a => by
    change ([a] : List (List ℕ)).flatten.Perm (a ++ [])
    rw [List.flatten_singleton, List.append_nil]
  | r :: rs, none => by
    change (passGoT rs (some r)).flatten.Perm ([] ++ (r ++ rs.flatten))
    exact passGoT_perm rs (some r)
  | r :: rs, some a => by
    change (mergeK a r ++ (passGoT rs none).flatten).Perm (a ++ (r ++ rs.flatten))
    rw [← List.append_assoc]
    exact (mergeK_permT a r).append (passGoT_perm rs none)

theorem flatten_singletonsT : ∀ (l : List ℕ), (l.map fun x => [x]).flatten = l
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.flatten_cons, flatten_singletonsT l]
    rfl

theorem sortK_perm (l : List ℕ) : (sortK l).Perm l := by
  have key : ∀ m, (Nat.rec (motive := fun _ => List (List ℕ)) (List.map (fun x => [x]) l)
      (fun _ ih => passK ih) m).flatten.Perm l := by
    intro m
    induction m with
    | zero =>
      change (List.map (fun x => [x]) l).flatten.Perm l
      rw [flatten_singletonsT]
    | succ m ih => exact (passGoT_perm _ none).trans ih
  exact key 13

@[expose] noncomputable def sincA (l : List ℕ) : Option ℕ → Bool :=
  List.rec (motive := fun _ => Option ℕ → Bool) (fun _ => true)
    (fun x _ ih o => andB (Option.rec (motive := fun _ => Bool) true (fun y => Nat.blt y x) o)
      (ih (some x))) l

theorem sincA_spec : ∀ (l : List ℕ) (o : Option ℕ), sincA l o = true →
    l.Nodup ∧ ∀ y ∈ o, ∀ x ∈ l, y < x
  | [], _, _ => ⟨List.nodup_nil, fun _ _ _ hx => absurd hx List.not_mem_nil⟩
  | x :: l, o, h => by
    have h' : andB (Option.rec (motive := fun _ => Bool) true (fun y => Nat.blt y x) o)
        (sincA l (some x)) = true := h
    rw [andB_iff] at h'
    obtain ⟨hl, hlt⟩ := sincA_spec l (some x) h'.2
    refine ⟨List.nodup_cons.2 ⟨fun hx => absurd (hlt x rfl x hx) (lt_irrefl x), hl⟩, ?_⟩
    intro y hy z hz
    cases o with
    | none => exact absurd hy (by simp)
    | some y' =>
      have hy' : y' = y := Option.some.inj hy
      subst hy'
      have hyx : y' < x := blt_iff.mp h'.1
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hyx
      · exact hyx.trans (hlt x rfl z hz)

theorem nodup_of_distinctS {l : List ℕ} (h : distinctS l = true) : l.Nodup :=
  (sortK_perm l).nodup_iff.mp (sincA_spec (sortK l) none h).1

theorem filtL_eqT (l : List ℕ) (f : ℕ → Bool) : filtL l f = l.filter f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Bool.rec (motive := fun _ => List ℕ) (filtL l f) (x :: filtL l f) (f x) = _
    rw [ih, List.filter_cons]
    cases f x <;> rfl

@[expose] noncomputable def dedupA (l : List ℕ) : List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
    (fun x _ ih acc => ih (Bool.rec (motive := fun _ => List ℕ) (List.cons x acc) acc (memL x acc))) l

theorem dedupA_spec : ∀ (l acc : List ℕ), acc.Nodup →
    (dedupA l acc).Nodup ∧ ∀ z, z ∈ dedupA l acc ↔ z ∈ acc ∨ z ∈ l
  | [], acc, h => ⟨h, fun z => by simp [dedupA]⟩
  | x :: l, acc, h => by
    have e : dedupA (x :: l) acc =
        dedupA l (Bool.rec (motive := fun _ => List ℕ) (x :: acc) acc (memL x acc)) := rfl
    rw [e]
    cases hm : memL x acc with
    | true =>
      have hx : x ∈ acc := (memL_iff x acc).mp hm
      obtain ⟨h1, h2⟩ := dedupA_spec l acc h
      refine ⟨h1, fun z => ?_⟩
      rw [h2, List.mem_cons]
      constructor
      · rintro (h | h)
        exacts [Or.inl h, Or.inr (Or.inr h)]
      · rintro (h | rfl | h)
        exacts [Or.inl h, Or.inl hx, Or.inr h]
    | false =>
      have hx : x ∉ acc := fun hx => by rw [(memL_iff x acc).mpr hx] at hm; exact absurd hm (by decide)
      obtain ⟨h1, h2⟩ := dedupA_spec l (x :: acc) (List.nodup_cons.2 ⟨hx, h⟩)
      refine ⟨h1, fun z => ?_⟩
      rw [h2, List.mem_cons, List.mem_cons]
      tauto

theorem card_toFinset_map {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (l : List α) : (l.map f).toFinset.card = l.toFinset.card := by
  rw [List.card_toFinset, List.card_toFinset, List.dedup_map_of_injective hf, List.length_map]

theorem lenL_dedupL (l : List ℕ) : lenL (dedupL l) = l.toFinset.card := by
  obtain ⟨h1, h2⟩ := dedupA_spec l [] List.nodup_nil
  have e : dedupL l = dedupA l [] := rfl
  rw [lenL_eq, e, ← List.toFinset_card_of_nodup h1]
  congr 1
  ext z
  simp [h2]

variable {n : ℕ}

@[expose] def letP (a b : Perm (Fin n)) : ℕ → Perm (Fin n)
  | 0 => a
  | 1 => b
  | 2 => a⁻¹
  | _ => b⁻¹

@[expose] def wordP (a b : Perm (Fin n)) (w : List ℕ) : Perm (Fin n) :=
  w.foldl (fun acc l => acc * letP a b l) 1

@[expose] def spanP : List (Perm (Fin n)) → List (Perm (Fin n))
  | [] => [1]
  | e :: l => spanP l ++ (spanP l).map (e * ·)

theorem tbl_letP (a b : Perm (Fin n)) (l : ℕ) : tbl (letP a b l) = letterT n (tbl a) (tbl b) l := by
  rcases l with _ | _ | _ | l
  · rfl
  · rfl
  · exact tbl_inv a
  · exact tbl_inv b

theorem tbl_wordP (a b : Perm (Fin n)) (w : List ℕ) :
    tbl (wordP a b w) = wordT n (tbl a) (tbl b) w := by
  unfold wordP wordT
  suffices h : ∀ acc : Perm (Fin n), tbl (w.foldl (fun acc l => acc * letP a b l) acc) =
      w.foldl (fun acc l => mulT acc (letterT n (tbl a) (tbl b) l)) (tbl acc) by
    rw [h, tbl_one]
  induction w with
  | nil => intro acc; rfl
  | cons l w ih =>
    intro acc
    rw [List.foldl_cons, List.foldl_cons, ih, tbl_mul, tbl_letP]

theorem code_letP (hn : n ≤ 32) (a b : Perm (Fin n)) (l : ℕ) :
    P.code (letP a b l) = letK n (P.code a) (P.code b) l := by
  rcases l with _ | _ | _ | l
  · rfl
  · rfl
  · exact (code_inv hn a).symm
  · have e : letK n (P.code a) (P.code b) (l + 3) = P.inv n (P.code b) := by
      simp [letK, brec]
    rw [e]
    exact (code_inv hn b).symm

@[expose] noncomputable def wordKA (n A B : ℕ) (w : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
    (fun l _ ih acc => ih (P.mul n acc (letK n A B l))) w

theorem code_wordP (hn : n ≤ 32) (a b : Perm (Fin n)) (w : List ℕ) :
    P.code (wordP a b w) = wordK n (P.code a) (P.code b) w := by
  have key : ∀ (w : List ℕ) (acc : Perm (Fin n)),
      P.code (w.foldl (fun acc l => acc * letP a b l) acc) =
        wordKA n (P.code a) (P.code b) w (P.code acc) := by
    intro w
    induction w with
    | nil => intro acc; rfl
    | cons l w ih =>
      intro acc
      rw [List.foldl_cons, ih]
      change _ = wordKA n (P.code a) (P.code b) w
        (P.mul n (P.code acc) (letK n (P.code a) (P.code b) l))
      rw [← code_letP hn, code_mul hn]
  have e : wordK n (P.code a) (P.code b) w = wordKA n (P.code a) (P.code b) w (P.one n) := rfl
  rw [e, code_one]
  exact key w 1

theorem tbl_spanP (l : List (Perm (Fin n))) : (spanP l).map tbl = spanT n (l.map tbl) := by
  induction l with
  | nil => simp [spanP, spanT, tbl_one]
  | cons e l ih =>
    simp only [spanP, spanT, List.map_cons, List.map_append, List.map_map, ← ih]
    congr 1
    apply List.map_congr_left
    intro y _
    exact tbl_mul _ _

theorem rec_mapT (m : ℕ → ℕ) (l : List ℕ) :
    List.rec (motive := fun _ => List ℕ) [] (fun x _ ih2 => List.cons (m x) ih2) l = l.map m := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change m x :: List.rec (motive := fun _ => List ℕ) [] (fun x _ ih2 => List.cons (m x) ih2) l = _
    rw [ih]
    rfl

theorem code_spanP (hn : n ≤ 32) (l : List (Perm (Fin n))) :
    (spanP l).map P.code = spanK n (l.map P.code) := by
  induction l with
  | nil =>
    change [P.code 1] = [P.one n]
    rw [code_one]
  | cons e l ih =>
    change _ = List.append (spanK n (l.map P.code)) (List.rec (motive := fun _ => List ℕ) []
      (fun x _ ih2 => List.cons (P.mul n (P.code e) x) ih2) (spanK n (l.map P.code)))
    rw [rec_mapT, ← ih, spanP, List.map_append, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro y _
    exact (code_mul hn e y).symm

theorem mem_spanP_cons (e : Perm (Fin n)) (l : List (Perm (Fin n))) (z : Perm (Fin n)) :
    z ∈ spanP (e :: l) ↔ z ∈ spanP l ∨ ∃ w ∈ spanP l, z = e * w := by
  simp only [spanP, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨w, hw, rfl⟩)
    exacts [Or.inl h, Or.inr ⟨w, hw, rfl⟩]
  · rintro (h | ⟨w, hw, rfl⟩)
    exacts [Or.inl h, Or.inr ⟨w, hw, rfl⟩]

theorem mem_spanP_two (e f : Perm (Fin n)) (l : List (Perm (Fin n))) (z : Perm (Fin n)) :
    z ∈ spanP (e :: f :: l) ↔
      ∃ w ∈ spanP l, z = w ∨ z = f * w ∨ z = e * w ∨ z = e * (f * w) := by
  rw [mem_spanP_cons]
  constructor
  · rintro (h | ⟨w, hw, rfl⟩)
    · rcases (mem_spanP_cons f l z).mp h with h | ⟨w, hw, rfl⟩
      exacts [⟨z, h, Or.inl rfl⟩, ⟨w, hw, Or.inr (Or.inl rfl)⟩]
    · rcases (mem_spanP_cons f l w).mp hw with h | ⟨v, hv, rfl⟩
      exacts [⟨w, h, Or.inr (Or.inr (Or.inl rfl))⟩, ⟨v, hv, Or.inr (Or.inr (Or.inr rfl))⟩]
  · rintro ⟨w, hw, rfl | rfl | rfl | rfl⟩
    · exact Or.inl ((mem_spanP_cons f l _).mpr (Or.inl hw))
    · exact Or.inl ((mem_spanP_cons f l _).mpr (Or.inr ⟨w, hw, rfl⟩))
    · exact Or.inr ⟨w, (mem_spanP_cons f l _).mpr (Or.inl hw), rfl⟩
    · exact Or.inr ⟨f * w, (mem_spanP_cons f l _).mpr (Or.inr ⟨w, hw, rfl⟩), rfl⟩

theorem mem_spanP_perm {l₁ l₂ : List (Perm (Fin n))} (hp : l₁.Perm l₂) :
    (∀ x ∈ l₁, ∀ y ∈ l₁, x * y = y * x) → ∀ z, z ∈ spanP l₁ ↔ z ∈ spanP l₂ := by
  induction hp with
  | nil => exact fun _ _ => Iff.rfl
  | cons e _ ih =>
    intro hc z
    have hc' : ∀ x ∈ _, ∀ y ∈ _, x * y = y * x :=
      fun x hx y hy => hc x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    rw [mem_spanP_cons, mem_spanP_cons, ih hc']
    simp only [ih hc']
  | swap e f l =>
    intro hc z
    have hef : f * e = e * f := hc f (by simp) e (by simp)
    rw [mem_spanP_two, mem_spanP_two]
    constructor
    · rintro ⟨w, hw, h | h | h | h⟩
      exacts [⟨w, hw, Or.inl h⟩, ⟨w, hw, Or.inr (Or.inr (Or.inl h))⟩,
        ⟨w, hw, Or.inr (Or.inl h)⟩, ⟨w, hw, Or.inr (Or.inr (Or.inr (by
          rw [h, ← mul_assoc, ← mul_assoc, hef])))⟩]
    · rintro ⟨w, hw, h | h | h | h⟩
      exacts [⟨w, hw, Or.inl h⟩, ⟨w, hw, Or.inr (Or.inr (Or.inl h))⟩,
        ⟨w, hw, Or.inr (Or.inl h)⟩, ⟨w, hw, Or.inr (Or.inr (Or.inr (by
          rw [h, ← mul_assoc, ← mul_assoc, hef])))⟩]
  | trans h₁ _ ih₁ ih₂ =>
    intro hc z
    exact (ih₁ hc z).trans (ih₂ (fun x hx y hy => hc x (h₁.mem_iff.mpr hx) y (h₁.mem_iff.mpr hy)) z)

theorem length_spanP (l : List (Perm (Fin n))) : (spanP l).length = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [spanP, List.length_append, List.length_map, ih, List.length_cons, pow_succ]
    ring

theorem spanP_one (l : List (Perm (Fin n))) (z : Perm (Fin n)) (h : z ∈ spanP (1 :: l)) :
    z ∈ spanP l := by
  rcases (mem_spanP_cons 1 l z).mp h with h | ⟨w, hw, rfl⟩
  · exact h
  · rwa [one_mul]

theorem spanP_dup (x : Perm (Fin n)) (l : List (Perm (Fin n))) (hx : x * x = 1) (z : Perm (Fin n))
    (h : z ∈ spanP (x :: x :: l)) : z ∈ spanP (x :: l) := by
  rcases (mem_spanP_cons x _ z).mp h with h | ⟨w, hw, rfl⟩
  · exact h
  · rcases (mem_spanP_cons x l w).mp hw with hw | ⟨v, hv, rfl⟩
    · exact (mem_spanP_cons x l _).mpr (Or.inr ⟨w, hw, rfl⟩)
    · rw [← mul_assoc, hx, one_mul]
      exact (mem_spanP_cons x l _).mpr (Or.inl hv)

theorem codeT_cons (x : ℕ) (t : List ℕ) : codeT (x :: t) = x + 32 * codeT t := rfl

theorem codeT_eq_E : ∀ t : List ℕ, codeT t = P.E (fun i => t.getD i 0) t.length
  | [] => by
    rw [List.length_nil, P.E_zero]
    rfl
  | x :: t => by
    rw [codeT_cons, List.length_cons, P.E_succ_left, codeT_eq_E t]
    rfl

theorem tabOK_perm (hn : n ≤ 32) {t : List ℕ} (h : tabOK n t = true) :
    ∃ σ : Perm (Fin n), tbl σ = t ∧ P.code σ = codeT t := by
  unfold tabOK at h
  rw [andB_iff, andB_iff, beq_iff, allL_iff, lenL_eq] at h
  obtain ⟨hl, hlt, hp⟩ := h
  obtain ⟨σ, hσ⟩ := exists_of_permK hp
  refine ⟨σ, ?_, hσ⟩
  apply List.ext_getElem (by rw [length_tbl, hl])
  intro i h1 h2
  have hi : i < n := by rwa [length_tbl] at h1
  have e1 : (tbl σ)[i] = P.vals σ i := by
    rw [← List.getD_eq_getElem _ 0 h1]
    exact (tbl_getD σ ⟨i, hi⟩).trans (P.vals_fin σ ⟨i, hi⟩).symm
  rw [e1, ← img_code' hn σ hi, hσ, img_eq, codeT_eq_E, P.E_digit ?_ h2,
    List.getD_eq_getElem _ _ h2]
  intro j hj
  rw [List.getD_eq_getElem _ _ hj]
  have := blt_iff.mp (hlt _ (List.getElem_mem hj))
  omega

theorem tabs_perm (hn : n ≤ 32) : ∀ ts : List (List ℕ), allT ts (tabOK n) = true →
    ∃ Es : List (Perm (Fin n)), Es.map tbl = ts ∧ Es.map P.code = ts.map codeT
  | [], _ => ⟨[], rfl, rfl⟩
  | t :: ts, h => by
    have h' : andB (tabOK n t) (allT ts (tabOK n)) = true := h
    rw [andB_iff] at h'
    obtain ⟨σ, h1, h2⟩ := tabOK_perm hn h'.1
    obtain ⟨Es, h3, h4⟩ := tabs_perm hn ts h'.2
    exact ⟨σ :: Es, by rw [List.map_cons, h1, h3], by rw [List.map_cons, h2, h4, List.map_cons]⟩

theorem memL_code (hn : n ≤ 32) (x : Perm (Fin n)) (L : List (Perm (Fin n))) :
    memL (P.code x) (L.map P.code) = true ↔ x ∈ L := by
  rw [memL_iff, mem_map_code hn]

theorem mem_tbl (x : Perm (Fin n)) (L : List (Perm (Fin n))) : tbl x ∈ L.map tbl ↔ x ∈ L := by
  rw [List.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => tbl_injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

theorem nodup_tbl_of {L : List (Perm (Fin n))} (h : (L.map P.code).Nodup) :
    (L.map tbl).Nodup :=
  (h.of_map _).map tbl_injective

theorem closed_of (hn : n ≤ 32) {L : List (Perm (Fin n))} (h : closedT n (L.map P.code) = true) :
    TabClosed n (L.map tbl) := by
  unfold closedT at h
  rw [andB_iff, andB_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [code_one, memL_code hn] at h1
    rw [← tbl_one]
    exact List.mem_map_of_mem h1
  · intro s hs t ht
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hs
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
    rw [allL_map] at h2
    have := h2 σ hσ
    rw [allL_map] at this
    have := this τ hτ
    rw [code_mul hn, memL_code hn] at this
    rw [← tbl_mul]
    exact List.mem_map_of_mem this
  · intro t ht
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
    rw [allL_map] at h3
    have := h3 τ hτ
    rw [code_inv hn, memL_code hn] at this
    rw [← tbl_inv]
    exact List.mem_map_of_mem this

theorem eok_of (hn : n ≤ 32) {L E : List (Perm (Fin n))}
    (h : eokT n (L.map P.code) (E.map P.code) = true) : EOK n (L.map tbl) (E.map tbl) := by
  unfold eokT at h
  simp only [allBs_cons, allBs_nil, andB_iff, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [distinctL_map hn] at h1
  rw [beq_iff, lenL_eq, List.length_map] at h2
  refine ⟨h1.map tbl_injective, by rw [List.length_map, h2], ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
    rw [allL_map] at h3
    exact (mem_tbl τ L).mpr ((memL_code hn τ L).mp (h3 τ hτ))
  · intro s hs t ht
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hs
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
    rw [allL_map] at h4
    have := h4 σ hσ
    rw [allL_map] at this
    exact (mul_comm_iff_tbl σ τ).mp ((comm_code hn σ τ).mp (this τ hτ))
  · intro t ht
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
    rw [allL_map] at h5
    have := h5 τ hτ
    rw [code_mul hn, code_one, beq_code hn] at this
    rw [← tbl_mul, this, tbl_one]

theorem selfCent_of (hn : n ≤ 32) {H E : List (Perm (Fin n))}
    (h : selfCentT n (H.map P.code) (E.map P.code) = true) : SelfCent (H.map tbl) (E.map tbl) := by
  intro t ht hc
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
  unfold selfCentT at h
  rw [allL_map] at h
  have := impB_iff.mp (h τ hτ)
  rw [memL_code hn] at this
  refine (mem_tbl τ E).mpr (this ?_)
  rw [allL_map]
  intro e he
  exact (comm_code hn τ e).mpr ((mul_comm_iff_tbl τ e).mpr (hc _ (List.mem_map_of_mem he)))

theorem wit_of (hn : n ≤ 32) {g : Perm (Fin n)} {E₁ E₂ : List (Perm (Fin n))}
    (h : witT n (P.code g) (E₁.map P.code) (E₂.map P.code) = true) :
    Wit n (tbl g) (E₁.map tbl) (E₂.map tbl) := by
  unfold witT at h
  rw [andB_iff, allL_map, anyL_map] at h
  obtain ⟨h1, e, he, h2⟩ := h
  refine ⟨fun t ht => ?_, ⟨tbl e, List.mem_map_of_mem he, ?_⟩⟩
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
    have := h1 τ hτ
    rw [conj_code hn, memL_code hn] at this
    rw [← tbl_conj]
    exact List.mem_map_of_mem this
  · rw [notB_iff, conj_code hn, memL_code hn] at h2
    rw [← tbl_conj, mem_tbl]
    exact h2

theorem allTail_suffix {l : List ℕ} {f : ℕ → List ℕ → Bool} (h : allTail l f = true) {x : ℕ}
    {r : List ℕ} (hs : List.IsSuffix (x :: r) l) : f x r = true := by
  induction l with
  | nil => exact absurd (List.eq_nil_of_suffix_nil hs) (List.cons_ne_nil _ _)
  | cons y l ih =>
    have h' : andB (f y l) (allTail l f) = true := h
    rw [andB_iff] at h'
    rcases List.suffix_cons_iff.mp hs with e | hs
    · rw [List.cons.inj e |>.1, List.cons.inj e |>.2]
      exact h'.1
    · exact ih h'.2 hs

theorem sub_cons_suffix {α : Type} : ∀ {l : List α} {x : α} {s : List α},
    List.Sublist (x :: s) l → ∃ r, List.IsSuffix (x :: r) l ∧ List.Sublist s r
  | [], _, _, h => absurd (List.eq_nil_of_sublist_nil h) (List.cons_ne_nil _ _)
  | y :: l, x, s, h => by
    cases h with
    | cons _ h' =>
      obtain ⟨r, hs, hr⟩ := sub_cons_suffix h'
      exact ⟨r, hs.trans (List.suffix_cons _ _), hr⟩
    | cons_cons _ h' => exact ⟨l, List.suffix_refl _, h'⟩

theorem classP (hn : n ≤ 32) {PP EA EB : List (Perm (Fin n))}
    (h : classT n (PP.map P.code) (EA.map P.code) (EB.map P.code) = true)
    (σs : List (Perm (Fin n))) (hlen : σs.length = 4) (hmem : ∀ σ ∈ σs, σ ∈ PP ∧ σ * σ = 1)
    (hcomm : ∀ σ ∈ σs, ∀ τ ∈ σs, σ * τ = τ * σ) :
    (spanP σs).toFinset.card < 16 ∨ (∀ x ∈ spanP σs, x ∈ EA) ∨ ∀ x ∈ spanP σs, x ∈ EB := by
  by_cases hgood : σs.Nodup ∧ ∀ σ ∈ σs, σ ≠ 1
  · set I := PP.filter fun t => decide (t ≠ 1 ∧ t * t = 1) with hI
    have hfilt : filtL (PP.map P.code) (fun t => andB (notB (Nat.beq t (P.one n)))
        (Nat.beq (P.mul n t t) (P.one n))) = I.map P.code := by
      rw [filtL_eqT, List.filter_map, hI]
      congr 1
      apply List.filter_congr
      intro t _
      rw [Bool.eq_iff_iff, Function.comp_apply, andB_iff, notB_iff, code_one, beq_code hn,
        code_mul hn, beq_code hn, decide_eq_true_iff]
    have hsub : σs ⊆ I := fun σ hσ => by
      rw [hI, List.mem_filter, decide_eq_true_iff]
      exact ⟨(hmem σ hσ).1, hgood.2 σ hσ, (hmem σ hσ).2⟩
    obtain ⟨τs, hperm, hsubl⟩ := List.subperm_of_subset hgood.1 hsub
    have hτlen : τs.length = 4 := hperm.length_eq.trans hlen
    have hτmem : ∀ τ ∈ τs, τ ∈ σs := fun τ hτ => hperm.mem_iff.mp hτ
    have hτc : ∀ σ ∈ τs, ∀ τ ∈ τs, P.comm n (P.code σ) (P.code τ) = true :=
      fun σ hσ τ hτ => (comm_code hn σ τ).mpr (hcomm σ (hτmem σ hσ) τ (hτmem τ hτ))
    have hspan : ∀ z, z ∈ spanP τs ↔ z ∈ spanP σs := mem_spanP_perm hperm
      (fun x hx y hy => hcomm x (hτmem x hx) y (hτmem y hy))
    obtain ⟨τ1, τ2, τ3, τ4, rfl⟩ : ∃ τ1 τ2 τ3 τ4, τs = [τ1, τ2, τ3, τ4] := by
      match τs, hτlen with
      | [τ1, τ2, τ3, τ4], _ => exact ⟨τ1, τ2, τ3, τ4, rfl⟩
    have hsubc := hsubl.map P.code
    unfold classT at h
    rw [hfilt] at h
    simp only [List.map_cons, List.map_nil] at hsubc
    obtain ⟨r1, hs1, hr1⟩ := sub_cons_suffix hsubc
    have k1 := allTail_suffix h hs1
    obtain ⟨r2, hs2, hr2⟩ := sub_cons_suffix hr1
    have k2 := impB_iff.mp (allTail_suffix k1 hs2) (hτc _ (by simp) _ (by simp))
    obtain ⟨r3, hs3, hr3⟩ := sub_cons_suffix hr2
    have k3 := impB_iff.mp (allTail_suffix k2 hs3)
      (andB_iff.mpr ⟨hτc _ (by simp) _ (by simp), hτc _ (by simp) _ (by simp)⟩)
    obtain ⟨r4, hs4, -⟩ := sub_cons_suffix hr3
    have k4 := impB_iff.mp (allTail_suffix k3 hs4)
      (andB_iff.mpr ⟨hτc _ (by simp) _ (by simp),
        andB_iff.mpr ⟨hτc _ (by simp) _ (by simp), hτc _ (by simp) _ (by simp)⟩⟩)
    have hsK : spanK n [P.code τ1, P.code τ2, P.code τ3, P.code τ4] =
        (spanP [τ1, τ2, τ3, τ4]).map P.code := by
      rw [code_spanP hn]
      rfl
    rw [hsK, orB_iff, orB_iff, blt_iff, lenL_dedupL, allL_map, allL_map] at k4
    have hfin : (spanP [τ1, τ2, τ3, τ4]).toFinset = (spanP σs).toFinset := by
      ext z
      rw [List.mem_toFinset, List.mem_toFinset, hspan]
    rcases k4 with k4 | k4 | k4
    · left
      rw [card_toFinset_map (fun _ _ e => code_inj hn e), hfin] at k4
      exact k4
    · right
      left
      intro x hx
      exact (memL_code hn x EA).mp (k4 x ((hspan x).mpr hx))
    · right
      right
      intro x hx
      exact (memL_code hn x EB).mp (k4 x ((hspan x).mpr hx))
  · left
    have hsmall : ∃ l' : List (Perm (Fin n)), l'.length = 3 ∧ ∀ z ∈ spanP σs, z ∈ spanP l' := by
      rw [not_and_or] at hgood
      rcases hgood with hdup | hone
      · rw [List.nodup_iff_sublist] at hdup
        push Not at hdup
        obtain ⟨x, hx⟩ := hdup
        obtain ⟨rest, hp⟩ := hx.exists_perm_append
        have hxm : x ∈ σs := hx.subset (by simp)
        refine ⟨x :: rest, ?_, fun z hz => spanP_dup x rest (hmem x hxm).2 z ?_⟩
        · have := hp.length_eq
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          simp only [List.length_cons]
          omega
        · exact (mem_spanP_perm hp hcomm z).mp hz
      · push Not at hone
        obtain ⟨σ, hσ, rfl⟩ := hone
        have hp := List.perm_cons_erase hσ
        refine ⟨σs.erase 1, ?_, fun z hz => spanP_one _ z ((mem_spanP_perm hp hcomm z).mp hz)⟩
        rw [List.length_erase_of_mem hσ, hlen]
    obtain ⟨l', hl', hsub⟩ := hsmall
    calc (spanP σs).toFinset.card ≤ (spanP l').toFinset.card :=
          Finset.card_le_card fun z hz => List.mem_toFinset.mpr (hsub z (List.mem_toFinset.mp hz))
      _ ≤ (spanP l').length := List.toFinset_card_le _
      _ < 16 := by rw [length_spanP, hl']; norm_num

theorem invs_perm {PP : List (Perm (Fin n))} {t : List ℕ} (ht : t ∈ invsOf n (PP.map tbl)) :
    ∃ σ ∈ PP, tbl σ = t ∧ σ * σ = 1 := by
  rw [invsOf, List.mem_filter, decide_eq_true_iff] at ht
  obtain ⟨hm, hsq⟩ := ht
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hm
  refine ⟨σ, hσ, rfl, tbl_injective ?_⟩
  rw [tbl_mul, hsq, tbl_one]

theorem class_of (hn : n ≤ 32) {PP EA EB : List (Perm (Fin n))}
    (h : classT n (PP.map P.code) (EA.map P.code) (EB.map P.code) = true) :
    ClassOK n (PP.map tbl) (EA.map tbl) (EB.map tbl) := by
  intro t1 h1 t2 h2 c12 t3 h3 c13 c23 t4 h4 c14 c24 c34
  obtain ⟨σ1, m1, rfl, q1⟩ := invs_perm h1
  obtain ⟨σ2, m2, rfl, q2⟩ := invs_perm h2
  obtain ⟨σ3, m3, rfl, q3⟩ := invs_perm h3
  obtain ⟨σ4, m4, rfl, q4⟩ := invs_perm h4
  rw [← mul_comm_iff_tbl] at c12 c13 c23 c14 c24 c34
  have hsp : spanT n [tbl σ1, tbl σ2, tbl σ3, tbl σ4] = (spanP [σ1, σ2, σ3, σ4]).map tbl := by
    rw [tbl_spanP]
    rfl
  rw [hsp]
  have key := classP hn h [σ1, σ2, σ3, σ4] rfl
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro σ (rfl | rfl | rfl | rfl)
        exacts [⟨m1, q1⟩, ⟨m2, q2⟩, ⟨m3, q3⟩, ⟨m4, q4⟩])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro σ (rfl | rfl | rfl | rfl) τ (rfl | rfl | rfl | rfl)
        all_goals first | rfl | assumption | exact Eq.symm ‹_›)
  rcases key with k | k | k
  · left
    rw [← List.card_toFinset, card_toFinset_map tbl_injective]
    exact k
  · right
    left
    intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    exact List.mem_map_of_mem (k x hx)
  · right
    right
    intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    exact List.mem_map_of_mem (k x hx)

theorem optRec_none {β : Type} (f : Bool) (g : β → Bool) :
    Option.rec (motive := fun _ => Bool) f g none = f := rfl

theorem optRec_some {β : Type} (f : Bool) (g : β → Bool) (x : β) :
    Option.rec (motive := fun _ => Bool) f g (some x) = g x := rfl

theorem check_soundK {n : ℕ} (hn : n ≤ 32) (D : Dat) (c₁ c₂ c₃ : List Char)
    (h₁ : D.clPar = parsePairs (String.ofList c₁)) (h₂ : D.hPar = parsePairs (String.ofList c₂))
    (h₃ : D.pPar = parsePairs (String.ofList c₃))
    (h : checkK n D.ta D.tb D.order c₁ D.hGensW c₂ D.pGensW c₃ D.eaGens D.ebGens D.gaW D.gbW =
      true) : Check n D := by
  unfold checkK at h
  cases hp1 : parseK c₁ with
  | none =>
    simp only [hp1] at h
    exact (Bool.false_ne_true h).elim
  | some clPar =>
  cases hp2 : parseK c₂ with
  | none =>
    simp only [hp1, hp2] at h
    exact (Bool.false_ne_true h).elim
  | some hPar =>
  cases hp3 : parseK c₃ with
  | none =>
    simp only [hp1, hp2, hp3] at h
    exact (Bool.false_ne_true h).elim
  | some pPar =>
  simp only [hp1, hp2, hp3] at h
  rw [letB_eq, letB_eq] at h
  have e1 : clPar = D.clPar := by rw [h₁]; exact parseK_sound hp1
  have e2 : hPar = D.hPar := by rw [h₂]; exact parseK_sound hp2
  have e3 : pPar = D.pPar := by rw [h₃]; exact parseK_sound hp3
  subst e1 e2 e3
  simp only [allBs_cons, allBs_nil, andB_iff, and_true] at h
  obtain ⟨m1, m2, m3, oka, okb, okEa, okEb, dcl, dH, hord, cH, dP, lP, oddP, clP, clEa, clEb,
    eA, eB, aEa, aEb, nAB, sA, sB, wA, wB, cls⟩ := h
  obtain ⟨a, hta, hca⟩ := tabOK_perm hn oka
  obtain ⟨b, htb, hcb⟩ := tabOK_perm hn okb
  obtain ⟨Ea0, hEa1, hEa2⟩ := tabs_perm hn D.eaGens okEa
  obtain ⟨Eb0, hEb1, hEb2⟩ := tabs_perm hn D.ebGens okEb
  set clPm := bfsG (fun x g => g * x * g⁻¹) 1 [a, b, a⁻¹, b⁻¹] a D.clPar with hclPm
  set HPm := bfsG (· * ·) 1 (D.hGensW.map (wordP a b)) 1 D.hPar with hHPm
  set PPm := bfsG (· * ·) 1 (D.pGensW.map (wordP a b)) 1 D.pPar with hPPm
  have hword : ∀ ws : List (List ℕ), ws.map (wordK n (P.code a) (P.code b)) =
      (ws.map (wordP a b)).map P.code := fun ws => by
    rw [List.map_map]
    exact List.map_congr_left fun w _ => (code_wordP hn a b w).symm
  have hwordT : ∀ ws : List (List ℕ), ws.map (wordT n (tbl a) (tbl b)) =
      (ws.map (wordP a b)).map tbl := fun ws => by
    rw [List.map_map]
    exact List.map_congr_left fun w _ => (tbl_wordP a b w).symm
  have ccl : bfsQ (fun x g => P.mul n (P.mul n g x) (P.inv n g)) (P.one n)
      [codeT D.ta, codeT D.tb, P.inv n (codeT D.ta), P.inv n (codeT D.tb)] (codeT D.ta) D.clPar =
      clPm.map P.code := by
    rw [bfsQ_eq _ _ _ _ _ m1, hclPm, bfsG_map P.code _ (fun x g => P.mul n (P.mul n g x) (P.inv n g))
      (fun x g => by rw [code_inv hn, code_mul hn, code_mul hn]), ← code_one, ← hca, ← hcb]
    simp only [List.map_cons, List.map_nil, code_inv hn]
  have cHl : bfsQ (P.mul n) (P.one n) (List.map (wordK n (codeT D.ta) (codeT D.tb)) D.hGensW)
      (P.one n) D.hPar = HPm.map P.code := by
    rw [bfsQ_eq _ _ _ _ _ m2, hHPm, bfsG_map P.code _ (P.mul n) (fun x g => (code_mul hn x g).symm),
      ← code_one, ← hca, ← hcb, hword]
  have cPl : bfsQ (P.mul n) (P.one n) (List.map (wordK n (codeT D.ta) (codeT D.tb)) D.pGensW)
      (P.one n) D.pPar = PPm.map P.code := by
    rw [bfsQ_eq _ _ _ _ _ m3, hPPm, bfsG_map P.code _ (P.mul n) (fun x g => (code_mul hn x g).symm),
      ← code_one, ← hca, ← hcb, hword]
  have cEa : spanK n (List.map codeT D.eaGens) = (spanP Ea0).map P.code := by
    rw [code_spanP hn, hEa2]
  have cEb : spanK n (List.map codeT D.ebGens) = (spanP Eb0).map P.code := by
    rw [code_spanP hn, hEb2]
  have tcl : D.cl n = clPm.map tbl := by
    rw [Dat.cl, bfs_eq_bfsG, hclPm, bfsG_map tbl _ (fun x g => conjT n g x)
      (fun x g => tbl_conj g x), tbl_one, hta, Dat.letters]
    simp only [List.map_cons, List.map_nil, tbl_inv, hta, htb]
  have tHl : D.Hl n = HPm.map tbl := by
    rw [Dat.Hl, bfs_eq_bfsG, hHPm, bfsG_map tbl _ mulT (fun x g => tbl_mul x g), tbl_one, Dat.hGens,
      ← hta, ← htb, hwordT]
  have tPl : D.Pl n = PPm.map tbl := by
    rw [Dat.Pl, bfs_eq_bfsG, hPPm, bfsG_map tbl _ mulT (fun x g => tbl_mul x g), tbl_one, Dat.pGens,
      ← hta, ← htb, hwordT]
  have tEa : D.Ea n = (spanP Ea0).map tbl := by rw [Dat.Ea, tbl_spanP, hEa1]
  have tEb : D.Eb n = (spanP Eb0).map tbl := by rw [Dat.Eb, tbl_spanP, hEb1]
  have tga : D.gaT n = tbl (wordP a b D.gaW) := by rw [Dat.gaT, tbl_wordP, hta, htb]
  have tgb : D.gbT n = tbl (wordP a b D.gbW) := by rw [Dat.gbT, tbl_wordP, hta, htb]
  rw [ccl] at dcl
  rw [cHl] at dH cH sA sB
  rw [cPl] at dP lP clP eA eB cls
  rw [cEa] at clEa eA aEa nAB sA wA wB cls
  rw [cEb] at clEb eB aEb nAB sB wA wB cls
  rw [ccl, cHl, lenL_eq, lenL_eq, List.length_map, List.length_map] at hord
  rw [← hca] at cH aEa aEb wA wB
  rw [← hcb] at wA wB
  rw [← code_wordP hn] at wA wB
  rw [lenL_eq, List.length_map] at lP
  have hPnd : PPm.Nodup := ((distinctL_map hn PPm).mp dP)
  unfold Check
  rw [tcl, tHl, tPl, tEa, tEb, tga, tgb, ← hta]
  refine ⟨nodup_tbl_of (nodup_of_distinctS dcl), nodup_tbl_of (nodup_of_distinctS dH),
    ?_, ?_, hPnd.map tbl_injective, ?_, ?_, closed_of hn clP, closed_of hn clEa, closed_of hn clEb,
    eok_of hn eA, eok_of hn eB, ?_, ?_, ?_, selfCent_of hn sA, selfCent_of hn sB, wit_of hn wA,
    wit_of hn wB, class_of hn cls⟩
  · rw [List.length_map, List.length_map]
    exact beq_iff.mp hord
  · intro t ht
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
    rw [allL_map] at cH
    exact (mul_comm_iff_tbl τ a).mp ((comm_code hn τ a).mp (cH τ hτ))
  · rw [List.length_map]
    exact beq_iff.mp lP
  · rw [beq_iff] at oddP
    change D.order / 128 % 2 = 1 at oddP
    omega
  · exact (mem_tbl a _).mpr ((memL_code hn a _).mp aEa)
  · exact (mem_tbl a _).mpr ((memL_code hn a _).mp aEb)
  · rw [anyL_map] at nAB
    obtain ⟨t, ht, hn'⟩ := nAB
    rw [notB_iff, memL_code hn] at hn'
    exact ⟨tbl t, List.mem_map_of_mem ht, fun h => hn' ((mem_tbl t _).mp h)⟩

end CFSG.KC.LQT.T2

end
