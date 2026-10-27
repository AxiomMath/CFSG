module

public import Certificates.Data.Kernel.TreeK

public section

namespace CFSG.KC.TreeK

inductive Reach (act : Nat → Nat → Nat) (ng root : Nat) : Nat → Prop
  | root : Reach act ng root root
  | step {x : Nat} (l : Nat) : l < ng → Reach act ng root x → Reach act ng root (act l x)

theorem andB_true {a b : Bool} (h : CFSG.KLie.CT.andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [CFSG.KLie.CT.andB]

@[expose] def QOK (F B : List Nat) : Prop := F = [] → B = []

theorem popQ_spec {F B : List Nat} (hq : QOK F B) :
    QOK (popQ F B).1 (popQ F B).2 ∧
      (popQ F B).1 ++ (popQ F B).2.reverse = (F ++ B.reverse).tail := by
  rcases F with _ | ⟨x, _ | ⟨y, F⟩⟩
  · rw [hq rfl]
    exact ⟨fun _ => rfl, rfl⟩
  · exact ⟨fun _ => rfl, by simp [popQ]⟩
  · exact ⟨fun h => absurd h (List.cons_ne_nil _ _), rfl⟩

theorem popsQ_spec (F B : List Nat) (hq : QOK F B) : ∀ k : Nat,
    QOK (popsQ k F B).1 (popsQ k F B).2 ∧
      (popsQ k F B).1 ++ (popsQ k F B).2.reverse = (F ++ B.reverse).drop k
  | 0 => ⟨hq, rfl⟩
  | k + 1 => by
    obtain ⟨hq', he⟩ := popsQ_spec F B hq k
    change QOK (popQ (popsQ k F B).1 (popsQ k F B).2).1 (popQ (popsQ k F B).1 (popsQ k F B).2).2 ∧ _
    obtain ⟨h1, h2⟩ := popQ_spec hq'
    refine ⟨h1, ?_⟩
    exact h2.trans (by rw [he, List.tail_drop])

theorem headQ_spec {F B : List Nat} (hq : QOK F B) {x : Nat} (hx : (F ++ B.reverse).head? = some x) :
    headQ F = x := by
  rcases F with _ | ⟨a, F⟩
  · rw [hq rfl] at hx
    exact absurd hx (by simp)
  · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hx
    exact hx

theorem pushQ_spec (y : Nat) {F B : List Nat} (hq : QOK F B) :
    QOK (pushQ y F B).1 (pushQ y F B).2 ∧
      (pushQ y F B).1 ++ (pushQ y F B).2.reverse = F ++ B.reverse ++ [y] := by
  rcases F with _ | ⟨a, F⟩
  · rw [hq rfl]
    exact ⟨fun h => absurd h (List.cons_ne_nil _ _), rfl⟩
  · exact ⟨fun h => absurd h (List.cons_ne_nil _ _), by simp [pushQ]⟩

theorem walkK_spec (act : Nat → Nat → Nat) (ng : Nat) : ∀ (recs : List (Nat × Nat))
    (h n : Nat) (F B acc : List Nat), acc.length = n → QOK F B → F ++ B.reverse = acc.reverse.drop h →
    (walkK act ng recs h n F B acc).2 = true →
    (∃ S, (walkK act ng recs h n F B acc).1.reverse = acc.reverse ++ S) ∧
      (walkK act ng recs h n F B acc).1.reverse.length = n + recs.length ∧
      ∀ j (hj : j < recs.length), recs[j].1 < n + j ∧ recs[j].2 < ng ∧
        (walkK act ng recs h n F B acc).1.reverse[n + j]? =
          ((walkK act ng recs h n F B acc).1.reverse[recs[j].1]?).map (act recs[j].2)
  | [], h, n, F, B, acc, hn, _, _, _ =>
    ⟨⟨[], (List.append_nil _).symm⟩, by simp [walkK, hn], fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | (p, l) :: rs, h, n, F, B, acc, hn, hq, he, hok => by
    have key : walkK act ng ((p, l) :: rs) h n F B acc =
        Bool.rec (motive := fun _ => List Nat × Bool) (acc, false)
          (walkK act ng rs p (n + 1)
            (pushQ (act l (headQ (popsQ (p - h) F B).1)) (popsQ (p - h) F B).1 (popsQ (p - h) F B).2).1
            (pushQ (act l (headQ (popsQ (p - h) F B).1)) (popsQ (p - h) F B).1 (popsQ (p - h) F B).2).2
            (act l (headQ (popsQ (p - h) F B).1) :: acc))
          (CFSG.KLie.CT.andB (Nat.ble h p) (CFSG.KLie.CT.andB (Nat.blt p n) (Nat.blt l ng))) := rfl
    rw [key] at hok ⊢
    cases hc : CFSG.KLie.CT.andB (Nat.ble h p) (CFSG.KLie.CT.andB (Nat.blt p n) (Nat.blt l ng)) with
    | false =>
      rw [hc] at hok
      exact absurd hok Bool.false_ne_true
    | true =>
      rw [hc] at hok
      change (walkK act ng rs p (n + 1) _ _ _).2 = true at hok
      change (∃ S, (walkK act ng rs p (n + 1) _ _ _).1.reverse = _) ∧ _
      obtain ⟨c1, c23⟩ := andB_true hc
      obtain ⟨c2, c3⟩ := andB_true c23
      have hhp : h ≤ p := Nat.le_of_ble_eq_true c1
      have hpn : p < n := Nat.le_of_ble_eq_true c2
      have hlg : l < ng := Nat.le_of_ble_eq_true c3
      obtain ⟨hq1, he1⟩ := popsQ_spec F B hq (p - h)
      rw [he, List.drop_drop, Nat.add_sub_cancel' hhp] at he1
      generalize popsQ (p - h) F B = Q at hok hq1 he1 ⊢
      have hpl : p < acc.reverse.length := by rw [List.length_reverse, hn]; exact hpn
      have hhead : headQ Q.1 = acc.reverse[p] := headQ_spec hq1 (by
        rw [he1, List.head?_drop, List.getElem?_eq_getElem hpl])
      rw [hhead] at hok ⊢
      generalize hy : act l acc.reverse[p] = y at hok ⊢
      obtain ⟨hq2, he2⟩ := pushQ_spec y hq1
      rw [he1] at he2
      have he2' : (pushQ y Q.1 Q.2).1 ++ (pushQ y Q.1 Q.2).2.reverse = (y :: acc).reverse.drop p := by
        rw [he2, List.reverse_cons, List.drop_append_of_le_length (Nat.le_of_lt hpl)]
      obtain ⟨⟨S, hS⟩, hlen, hst⟩ := walkK_spec act ng rs p (n + 1) _ _ (y :: acc)
        (by rw [List.length_cons, hn]) hq2 he2' hok
      rw [List.reverse_cons, List.append_assoc] at hS
      refine ⟨⟨_, hS⟩, by rw [hlen, List.length_cons]; omega, ?_⟩
      intro j hj
      cases j with
      | zero =>
        refine ⟨hpn, hlg, ?_⟩
        change _ = (_[p]?).map (act l)
        rw [hS, List.getElem?_append_left hpl, List.getElem?_eq_getElem hpl, Option.map_some, hy,
          Nat.add_zero, List.getElem?_append_right (by simp [hn]),
          List.length_reverse, hn, Nat.sub_self]
        rfl
      | succ j =>
        obtain ⟨a1, a2, a3⟩ := hst j (by simpa using hj)
        refine ⟨by simp only [List.getElem_cons_succ]; omega, by simpa using a2, ?_⟩
        simp only [List.getElem_cons_succ]
        rw [← a3]
        congr 1
        omega

theorem treePts_sound {act : Nat → Nat → Nat} {ng root : Nat} {recs : List (Nat × Nat)}
    (h : (treePts act ng root recs).2 = true) :
    (treePts act ng root recs).1.length = recs.length + 1 ∧
      (treePts act ng root recs).1[0]? = some root ∧
      ∀ i (hi : i < recs.length), recs[i].1 ≤ i ∧ recs[i].2 < ng ∧
        (treePts act ng root recs).1[i + 1]? =
          ((treePts act ng root recs).1[recs[i].1]?).map (act recs[i].2) := by
  change (walkK act ng recs 0 1 [root] [] [root]).2 = true at h
  change (walkK act ng recs 0 1 [root] [] [root]).1.reverse.length = _ ∧
    (walkK act ng recs 0 1 [root] [] [root]).1.reverse[0]? = _ ∧
    ∀ i (hi : i < recs.length), _ ∧ _ ∧ (walkK act ng recs 0 1 [root] [] [root]).1.reverse[i + 1]? =
      ((walkK act ng recs 0 1 [root] [] [root]).1.reverse[recs[i].1]?).map (act recs[i].2)
  obtain ⟨⟨S, hS⟩, hlen, hst⟩ := walkK_spec act ng recs 0 1 [root] [] [root] rfl (fun _ => rfl) rfl h
  refine ⟨by rw [hlen]; omega, by rw [hS]; rfl, fun i hi => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hst i hi
  refine ⟨by omega, a2, ?_⟩
  rw [Nat.add_comm i 1]
  exact a3

theorem spanLt_perm (x : Nat) (k : List Nat → List Nat → List Nat) : ∀ (ys acc : List Nat),
    ∃ p r, spanLt x ys k acc = k p r ∧ (p ++ r).Perm (acc ++ ys)
  | [], acc => ⟨acc.reverse, [], rfl, by
      rw [List.append_nil, List.append_nil]
      exact List.reverse_perm acc⟩
  | y :: ys', acc => by
    change ∃ p r, Bool.rec (motive := fun _ => List Nat) (k (List.reverse acc) (List.cons y ys'))
      (spanLt x ys' k (List.cons y acc)) (Nat.blt y x) = k p r ∧ (p ++ r).Perm (acc ++ y :: ys')
    cases Nat.blt y x
    · exact ⟨acc.reverse, y :: ys', rfl, (List.reverse_perm acc).append_right _⟩
    · obtain ⟨p, r, e, hp⟩ := spanLt_perm x k ys' (y :: acc)
      exact ⟨p, r, e, hp.trans List.perm_middle.symm⟩

theorem mergeK_perm : ∀ (xs ys : List Nat), (mergeK xs ys).Perm (xs ++ ys)
  | [], ys => List.Perm.refl ys
  | x :: xs, ys => by
    change (spanLt x ys (fun p r => List.append p (List.cons x (mergeK xs r))) []).Perm _
    obtain ⟨p, r, e, hp⟩ := spanLt_perm x (fun p r => List.append p (List.cons x (mergeK xs r))) ys []
    rw [e]
    rw [List.nil_append] at hp
    change (p ++ x :: mergeK xs r).Perm (x :: (xs ++ ys))
    refine (((mergeK_perm xs r).cons x).append_left p).trans (List.perm_middle.trans ?_)
    refine List.Perm.cons x ?_
    rw [← List.append_assoc]
    exact (List.perm_append_comm.append_right r).trans (by rw [List.append_assoc]; exact hp.append_left xs)

@[expose] noncomputable def passGo (rs : List (List Nat)) (o : Option (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => Option (List Nat) → List (List Nat))
    (fun o => Option.rec (motive := fun _ => List (List Nat)) [] (fun a => [a]) o)
    (fun r _ ih o => Option.rec (motive := fun _ => List (List Nat)) (ih (some r))
      (fun a => List.cons (mergeK a r) (ih none)) o) rs o

theorem passGo_perm : ∀ (rs : List (List Nat)) (o : Option (List Nat)),
    (passGo rs o).flatten.Perm (o.getD [] ++ rs.flatten)
  | [], none => List.Perm.refl _
  | [], some a => by
    change ([a] : List (List Nat)).flatten.Perm (a ++ [])
    rw [List.flatten_singleton, List.append_nil]
  | r :: rs, none => by
    change (passGo rs (some r)).flatten.Perm ([] ++ (r ++ rs.flatten))
    exact passGo_perm rs (some r)
  | r :: rs, some a => by
    change (mergeK a r ++ (passGo rs none).flatten).Perm (a ++ (r ++ rs.flatten))
    rw [← List.append_assoc]
    exact (mergeK_perm a r).append (passGo_perm rs none)

theorem flatten_singletons : ∀ (l : List Nat), (l.map fun x => [x]).flatten = l
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.flatten_cons, flatten_singletons l]
    rfl

theorem sortP_perm (np : Nat) (xs : List Nat) : (sortP np xs).Perm xs := by
  have key : ∀ n, (Nat.rec (motive := fun _ => List (List Nat)) (List.map (fun x => [x]) xs)
      (fun _ ih => passK ih) n).flatten.Perm xs := by
    intro n
    induction n with
    | zero =>
      change (List.map (fun x => [x]) xs).flatten.Perm xs
      rw [flatten_singletons]
    | succ n ih => exact (passGo_perm _ none).trans ih
  exact key np

@[expose] noncomputable def sincGo (l : List Nat) (o : Option Nat) : Bool :=
  List.rec (motive := fun _ => Option Nat → Bool) (fun _ => true)
    (fun x _ ih o => CFSG.KLie.CT.andB (Option.rec (motive := fun _ => Bool) true (fun y => Nat.blt y x) o)
      (ih (some x))) l o

theorem sincGo_sound : ∀ (l : List Nat) (o : Option Nat), sincGo l o = true →
    l.Nodup ∧ ∀ y ∈ l, ∀ b ∈ o, b < y
  | [], _, _ => ⟨List.nodup_nil, fun _ hy => absurd hy List.not_mem_nil⟩
  | x :: l, o, h => by
    change CFSG.KLie.CT.andB (Option.rec (motive := fun _ => Bool) true (fun y => Nat.blt y x) o)
      (sincGo l (some x)) = true at h
    have h1 : Option.rec (motive := fun _ => Bool) true (fun y => Nat.blt y x) o = true := by
      revert h
      cases Option.rec (motive := fun _ => Bool) true (fun y => Nat.blt y x) o <;> simp [CFSG.KLie.CT.andB]
    have h2 : sincGo l (some x) = true := by
      revert h
      cases Option.rec (motive := fun _ => Bool) true (fun y => Nat.blt y x) o <;> simp [CFSG.KLie.CT.andB]
    obtain ⟨hnd, hlt⟩ := sincGo_sound l (some x) h2
    have hox : ∀ b ∈ o, b < x := by
      intro b hb
      rw [Option.mem_def] at hb
      subst hb
      exact Nat.le_of_ble_eq_true h1
    refine ⟨List.nodup_cons.2 ⟨fun hx => Nat.lt_irrefl x (hlt x hx x rfl), hnd⟩, ?_⟩
    intro y hy b hb
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact hox b hb
    · exact Nat.lt_trans (hox b hb) (hlt y hy' x rfl)

theorem distinctK_sound {np : Nat} {xs : List Nat} (h : distinctK np xs = true) : xs.Nodup :=
  (sortP_perm np xs).nodup_iff.1 (sincGo_sound _ none h).1

theorem closedK_sound {act : Nat → Nat → Nat} {ng np : Nat} {xs : List Nat}
    (h : closedK act ng np xs = true) : ∀ x ∈ xs, ∀ l < ng, act l x ∈ xs := by
  have hsub : ∀ (as bs : List Nat), subS as bs = true → ∀ a ∈ as, a ∈ bs := by
    intro as
    induction as with
    | nil => intro _ _ a ha; exact absurd ha List.not_mem_nil
    | cons x as ih =>
      intro bs
      induction bs with
      | nil => intro hb; exact absurd hb Bool.false_ne_true
      | cons y ys ihy =>
        intro hb a ha
        change Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (subS (x :: as) ys) (Nat.blt y x)) (subS as (y :: ys)) (Nat.beq x y) = true at hb
        cases hxy : Nat.beq x y with
        | true =>
          rw [hxy] at hb
          rcases List.mem_cons.1 ha with rfl | ha'
          · rw [Nat.eq_of_beq_eq_true hxy]; exact List.mem_cons_self
          · exact ih _ hb a ha'
        | false =>
          rw [hxy] at hb
          cases hyx : Nat.blt y x with
          | true =>
            rw [hyx] at hb
            exact List.mem_cons_of_mem y (ihy hb a ha)
          | false =>
            rw [hyx] at hb
            exact absurd hb Bool.false_ne_true
  have himg : ∀ (ys : List Nat), ∀ x ∈ ys, ∀ l < ng, act l x ∈ imagesK act ng ys := by
    intro ys
    induction ys with
    | nil => intro x hx; exact absurd hx List.not_mem_nil
    | cons y ys ih =>
      intro x hx l hl
      have hgo : ∀ (m : Nat) (acc : List Nat), (∀ z ∈ acc, z ∈ Nat.rec (motive := fun _ => List Nat) acc
          (fun l acc => List.cons (act l y) acc) m) ∧ ∀ l < m, act l y ∈ Nat.rec
          (motive := fun _ => List Nat) acc (fun l acc => List.cons (act l y) acc) m := by
        intro m acc
        induction m with
        | zero => exact ⟨fun z hz => hz, fun l hl => absurd hl (Nat.not_lt_zero _)⟩
        | succ m ihm =>
          refine ⟨fun z hz => List.mem_cons_of_mem _ (ihm.1 z hz), fun l hl => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl' | rfl
          · exact List.mem_cons_of_mem _ (ihm.2 l hl')
          · exact List.mem_cons_self
      change act l x ∈ Nat.rec (motive := fun _ => List Nat) (imagesK act ng ys)
        (fun l acc => List.cons (act l y) acc) ng
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact (hgo ng _).2 l hl
      · exact (hgo ng _).1 _ (ih x hx' l hl)
  have h' : CFSG.KLie.CT.andB (sincK (sortP np xs)) (subS (sortP np (imagesK act ng xs)) (sortP np xs)) =
    true := h
  have h2 := (andB_true h').2
  intro x hx l hl
  have := hsub _ _ h2 (act l x) ((sortP_perm np _).mem_iff.2 (himg xs x hx l hl))
  exact (sortP_perm np xs).mem_iff.1 this

theorem treePts_reach {act : Nat → Nat → Nat} {ng root : Nat} {recs : List (Nat × Nat)}
    (h : (treePts act ng root recs).2 = true) :
    ∀ x ∈ (treePts act ng root recs).1, Reach act ng root x := by
  obtain ⟨hlen, h0, hstep⟩ := treePts_sound h
  generalize (treePts act ng root recs).1 = xs at hlen h0 hstep ⊢
  have key : ∀ i (hi : i < xs.length), Reach act ng root xs[i] := by
    intro i
    induction i using Nat.strongRecOn with
    | _ i ih =>
      intro hi
      cases i with
      | zero =>
        have : xs[0] = root := by
          rw [List.getElem?_eq_getElem hi] at h0
          exact Option.some.inj h0
        rw [this]
        exact Reach.root
      | succ i =>
        have hi' : i < recs.length := by omega
        obtain ⟨hp, hl, hx⟩ := hstep i hi'
        have hpl : recs[i].1 < xs.length := by omega
        rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hpl, Option.map_some] at hx
        rw [Option.some.inj hx]
        exact Reach.step _ hl (ih _ (by omega) hpl)
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact key i hi

theorem treeOK_sound {act : Nat → Nat → Nat} {ng np root : Nat} {recs : List (Nat × Nat)}
    (h : treeOK act ng np root recs = true) :
    (treePts act ng root recs).1.Nodup ∧
      (treePts act ng root recs).1.length = recs.length + 1 ∧
      ∀ x ∈ (treePts act ng root recs).1, Reach act ng root x := by
  have h' : (treePts act ng root recs).2 = true ∧ distinctK np (treePts act ng root recs).1 = true := by
    revert h
    rw [treeOK]
    rcases treePts act ng root recs with ⟨xs, ok⟩
    cases ok <;> simp [CFSG.KLie.CT.andB]
  exact ⟨distinctK_sound h'.2, (treePts_sound h'.1).1, treePts_reach h'.1⟩

end CFSG.KC.TreeK

end
