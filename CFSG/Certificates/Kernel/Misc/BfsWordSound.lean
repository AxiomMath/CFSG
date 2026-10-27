module

public import Mathlib.Data.Finset.Card

public section

namespace CFSG.KS.Bfs

@[expose] def bfsT (n m s : ℕ) (adj : Array (Array ℕ)) : Array ℕ × Array ℕ := Id.run do
  let mut par : Array ℕ := Array.replicate n n
  let mut gl : Array ℕ := Array.replicate n 0
  let mut queue : Array ℕ := #[s]
  par := par.set! s s
  let mut head := 0
  for _ in [0:n] do
    if head < queue.size then
      let x := queue[head]!
      head := head + 1
      for k in [0:m] do
        let y := (adj[k]!)[x]!
        if par[y]! == n then
          par := par.set! y x
          gl := gl.set! y k
          queue := queue.push y
  return (par, gl)

@[expose] def wordT (n s : ℕ) (par gl : Array ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, j =>
    if j == s then [] else if par[j]! == n then [] else gl[j]! :: wordT n s par gl fuel par[j]!

@[expose] def walkT (adj : Array (Array ℕ)) : List ℕ → ℕ → ℕ
  | [], x => x
  | k :: w, x => (adj[k]!)[walkT adj w x]!

theorem forIn_yield {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (h : ∀ a b, f a b = ForInStep.yield (g b a)) :
    forIn l init f = (l.foldl g init : β) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, h]
    exact ih _

@[expose] def inner (n : ℕ) (adj : Array (Array ℕ)) (x : ℕ) (st : Array ℕ × Array ℕ × Array ℕ)
    (k : ℕ) : Array ℕ × Array ℕ × Array ℕ :=
  if (st.1[(adj[k]!)[x]!]! == n) = true then
    (st.1.set! (adj[k]!)[x]! x, st.2.1.set! (adj[k]!)[x]! k, st.2.2.push (adj[k]!)[x]!)
  else (st.1, st.2.1, st.2.2)

@[expose] def outer (n m : ℕ) (adj : Array (Array ℕ)) (st : Array ℕ × Array ℕ × Array ℕ × ℕ)
    (_ : ℕ) : Array ℕ × Array ℕ × Array ℕ × ℕ :=
  if st.2.2.2 < st.2.2.1.size then
    let r := (List.range' 0 m).foldl (inner n adj st.2.2.1[st.2.2.2]!) (st.1, st.2.1, st.2.2.1)
    (r.1, r.2.1, r.2.2, st.2.2.2 + 1)
  else (st.1, st.2.1, st.2.2.1, st.2.2.2)

@[expose] def initS (n s : ℕ) : Array ℕ × Array ℕ × Array ℕ × ℕ :=
  ((Array.replicate n n).set! s s, Array.replicate n 0, #[s], 0)

theorem bfsT_eq (n m s : ℕ) (adj : Array (Array ℕ)) :
    bfsT n m s adj = (((List.range' 0 n).foldl (outer n m adj) (initS n s)).1,
      ((List.range' 0 n).foldl (outer n m adj) (initS n s)).2.1) := by
  unfold bfsT
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yield _ _ _ (outer n m adj)]
  · rfl
  · intro a st
    by_cases hc : st.2.2.2 < st.2.2.1.size
    · simp only [outer, hc, ↓reduceIte]
      rw [forIn_yield _ _ _ (inner n adj st.2.2.1[st.2.2.2]!)]
      · rfl
      · intro k st'
        unfold inner
        by_cases hk : (st'.1[(adj[k]!)[st.2.2.1[st.2.2.2]!]!]! == n) = true <;>
          simp only [hk, ↓reduceIte] <;> rfl
    · simp only [outer, hc, ↓reduceIte]
      rfl

theorem mem_iff_get (q : Array ℕ) (y : ℕ) : y ∈ q.toList ↔ ∃ t < q.size, q[t]! = y := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by rw [getElem!_pos q t ht, Array.getElem_toList]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by rw [getElem!_pos q t ht, Array.getElem_toList]⟩

theorem get_mem (q : Array ℕ) {t : ℕ} (ht : t < q.size) : q[t]! ∈ q.toList :=
  (mem_iff_get q _).2 ⟨t, ht, rfl⟩

theorem push_lt (q : Array ℕ) (y : ℕ) {t : ℕ} (ht : t < q.size) : (q.push y)[t]! = q[t]! := by
  rw [getElem!_pos (q.push y) t (by simp; omega), getElem!_pos q t ht, Array.getElem_push_lt ht]

theorem push_eq (q : Array ℕ) (y : ℕ) : (q.push y)[q.size]! = y := by
  rw [getElem!_pos (q.push y) q.size (by simp), Array.getElem_push_eq]

structure Inv (n m s : ℕ) (adj : Array (Array ℕ)) (par gl q : Array ℕ) : Prop where
  psz : par.size = n
  gsz : gl.size = n
  qlt : ∀ y ∈ q.toList, y < n
  q0 : q[0]! = s
  qpos : 0 < q.size
  reach : ∀ y < n, (par[y]! ≠ n ↔ y ∈ q.toList)
  tree : ∀ t < q.size, 0 < t → ∃ t' < t, q[t']! = par[q[t]!]! ∧ gl[q[t]!]! < m ∧
    (adj[gl[q[t]!]!]!)[par[q[t]!]!]! = q[t]!
  nodup : q.toList.Nodup

structure IInv (n m s : ℕ) (adj : Array (Array ℕ)) (q₀ : Array ℕ) (x k : ℕ)
    (st : Array ℕ × Array ℕ × Array ℕ) : Prop where
  inv : Inv n m s adj st.1 st.2.1 st.2.2
  sz : q₀.size ≤ st.2.2.size
  pre : ∀ t < q₀.size, st.2.2[t]! = q₀[t]!
  done : ∀ k' < k, (adj[k']!)[x]! ∈ st.2.2.toList

theorem inner_step {n m s : ℕ} {adj : Array (Array ℕ)} (hadj : ∀ k < m, ∀ x < n, (adj[k]!)[x]! < n)
    {q₀ : Array ℕ} {h : ℕ} (hh : h < q₀.size) {k : ℕ} (hk : k < m)
    {st : Array ℕ × Array ℕ × Array ℕ} (I : IInv n m s adj q₀ q₀[h]! k st) :
    IInv n m s adj q₀ q₀[h]! (k + 1) (inner n adj q₀[h]! st k) := by
  obtain ⟨par, gl, q⟩ := st
  obtain ⟨⟨psz, gsz, qlt, q0, qpos, reach, tree, nodup⟩, sz, pre, done⟩ := I
  dsimp only at psz gsz qlt q0 qpos reach tree nodup sz pre done
  set x := q₀[h]! with hx
  have xq : x ∈ q.toList := by
    rw [hx, ← pre h hh]
    exact get_mem q (by omega)
  have xn : x < n := qlt x xq
  set y := (adj[k]!)[x]! with hy
  have yn : y < n := hadj k hk x xn
  unfold inner
  by_cases hc : (par[y]! == n) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    dsimp only
    have pyn : par[y]! = n := beq_iff_eq.1 hc
    have ynq : y ∉ q.toList := fun hm => (reach y yn).2 hm pyn
    have qne : ∀ z ∈ q.toList, y ≠ z := fun z hz e => ynq (e ▸ hz)
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [Array.size_set!, psz]
    · rw [Array.size_set!, gsz]
    · intro z hz
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact qlt z hz
      · exact yn
    · rw [push_lt q y qpos, q0]
    · simp
    · intro z hz
      rw [Array.toList_push, List.mem_append, List.mem_singleton]
      by_cases e : z = y
      · subst e
        rw [Array.getElem!_set!_self _ _ _ (by rw [psz]; exact yn)]
        exact ⟨fun _ => Or.inr rfl, fun _ => by omega⟩
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm e), reach z hz]
        exact ⟨Or.inl, fun h' => h'.resolve_right e⟩
    · intro t ht tpos
      rw [Array.size_push] at ht
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht' | rfl
      · obtain ⟨t', ht't, e1, e2, e3⟩ := tree t ht' tpos
        have zq := get_mem q ht'
        have hne := qne _ zq
        rw [push_lt q y ht', Array.getElem!_set!_ne _ _ _ _ hne, Array.getElem!_set!_ne _ _ _ _ hne]
        exact ⟨t', ht't, by rw [push_lt q y (by omega), e1], e2, e3⟩
      · rw [push_eq, Array.getElem!_set!_self _ _ _ (by rw [psz]; exact yn),
          Array.getElem!_set!_self _ _ _ (by rw [gsz]; exact yn)]
        refine ⟨h, by omega, ?_, hk, rfl⟩
        rw [push_lt q y (by omega), pre h hh]
    · rw [Array.toList_push, List.nodup_append]
      refine ⟨nodup, by simp, fun a ha b hb e => ynq ?_⟩
      rw [List.mem_singleton] at hb
      have e' : a = y := e.trans hb
      rw [← e']
      exact ha
    · rw [Array.size_push]
      omega
    · intro t ht
      rw [push_lt q y (by omega), pre t ht]
    · intro k' hk'
      rw [Array.toList_push, List.mem_append, List.mem_singleton]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk'' | rfl
      · exact Or.inl (done k' hk'')
      · exact Or.inr rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    dsimp only
    refine ⟨⟨psz, gsz, qlt, q0, qpos, reach, tree, nodup⟩, sz, pre, fun k' hk' => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk'' | rfl
    · exact done k' hk''
    · refine (reach y yn).1 fun e => hc ?_
      rw [e]
      exact beq_self_eq_true n

theorem inner_loop {n m s : ℕ} {adj : Array (Array ℕ)}
    (hadj : ∀ k < m, ∀ x < n, (adj[k]!)[x]! < n) {q₀ : Array ℕ} {h : ℕ} (hh : h < q₀.size) :
    ∀ (c a : ℕ), a + c ≤ m → ∀ st, IInv n m s adj q₀ q₀[h]! a st →
      IInv n m s adj q₀ q₀[h]! (a + c) ((List.range' a c).foldl (inner n adj q₀[h]!) st)
  | 0, a, _, st, I => I
  | c + 1, a, hc, st, I => by
    rw [List.range'_succ, List.foldl_cons]
    have := inner_loop hadj hh c (a + 1) (by omega) _ (inner_step hadj hh (by omega) I)
    rwa [Nat.add_right_comm, Nat.add_assoc] at this

structure OInv (n m s : ℕ) (adj : Array (Array ℕ)) (a : ℕ) (st : Array ℕ × Array ℕ × Array ℕ × ℕ) :
    Prop where
  inv : Inv n m s adj st.1 st.2.1 st.2.2.1
  hle : st.2.2.2 ≤ st.2.2.1.size
  closed : ∀ t < st.2.2.2, ∀ k < m, (adj[k]!)[st.2.2.1[t]!]! ∈ st.2.2.1.toList
  cnt : st.2.2.2 = st.2.2.1.size ∨ a ≤ st.2.2.2

theorem outer_step {n m s : ℕ} {adj : Array (Array ℕ)} (hadj : ∀ k < m, ∀ x < n, (adj[k]!)[x]! < n)
    {a : ℕ} {st : Array ℕ × Array ℕ × Array ℕ × ℕ} (I : OInv n m s adj a st) :
    OInv n m s adj (a + 1) (outer n m adj st a) := by
  obtain ⟨par, gl, q, h⟩ := st
  obtain ⟨inv, hle, closed, cnt⟩ := I
  dsimp only at inv hle closed cnt
  unfold outer
  dsimp only
  by_cases hc : h < q.size
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    have I0 : IInv n m s adj q q[h]! 0 (par, gl, q) :=
      ⟨inv, Nat.le_refl _, fun _ _ => rfl, fun _ h' => absurd h' (Nat.not_lt_zero _)⟩
    have I1 := inner_loop hadj hc m 0 (by omega) _ I0
    rw [Nat.zero_add] at I1
    obtain ⟨inv', sz', pre', done'⟩ := I1
    refine ⟨inv', ?_, ?_, ?_⟩
    · dsimp only
      omega
    · dsimp only
      intro t ht k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht' | rfl
      · rw [pre' t (by omega)]
        obtain ⟨t'', ht'', e⟩ := (mem_iff_get q _).1 (closed t ht' k hk)
        rw [mem_iff_get]
        exact ⟨t'', by omega, by rw [pre' t'' ht'', e]⟩
      · rw [pre' t hc]
        exact done' k hk
    · right
      have := cnt.resolve_left (by omega)
      change a + 1 ≤ h + 1
      omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    exact ⟨inv, hle, closed, Or.inl (Nat.le_antisymm hle (Nat.not_lt.1 hc))⟩

theorem outer_loop {n m s : ℕ} {adj : Array (Array ℕ)} (hadj : ∀ k < m, ∀ x < n, (adj[k]!)[x]! < n) :
    ∀ (c a : ℕ) (st : Array ℕ × Array ℕ × Array ℕ × ℕ), OInv n m s adj a st →
      OInv n m s adj (a + c) ((List.range' a c).foldl (outer n m adj) st)
  | 0, a, st, I => I
  | c + 1, a, st, I => by
    rw [List.range'_succ, List.foldl_cons]
    have := outer_loop hadj c (a + 1) _ (outer_step hadj I)
    rwa [Nat.add_right_comm, Nat.add_assoc] at this

theorem init_inv {n m s : ℕ} {adj : Array (Array ℕ)} (hs : s < n) : OInv n m s adj 0 (initS n s) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp only [initS]
  · rw [Array.size_set!, Array.size_replicate]
  · rw [Array.size_replicate]
  · intro y hy
    simp only [List.mem_singleton] at hy
    rw [hy]
    exact hs
  · rfl
  · simp
  · intro y hy
    simp only [List.mem_singleton]
    by_cases e : y = s
    · subst e
      rw [Array.getElem!_set!_self _ _ _ (by rw [Array.size_replicate]; exact hy)]
      exact ⟨fun _ => rfl, fun _ => by omega⟩
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm e),
        getElem!_pos _ y (by rw [Array.size_replicate]; exact hy), Array.getElem_replicate]
      exact ⟨fun h' => absurd rfl h', fun h' => absurd h' e⟩
  · intro t ht tpos
    simp at ht
    omega
  · simp
  · simp
  · intro t ht
    omega
  · right
    exact Nat.le_refl _

theorem size_le {n m s : ℕ} {adj : Array (Array ℕ)} {par gl q : Array ℕ}
    (I : Inv n m s adj par gl q) : q.size ≤ n := by
  have h1 : q.toList.toFinset ⊆ Finset.range n := fun y hy => by
    rw [List.mem_toFinset] at hy
    exact Finset.mem_range.2 (I.qlt y hy)
  have h2 := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup I.nodup, Finset.card_range, Array.length_toList] at h2
  exact h2

theorem word_ok {n m s : ℕ} {adj : Array (Array ℕ)} {par gl q : Array ℕ}
    (I : Inv n m s adj par gl q) : ∀ t, t < q.size → ∀ fuel, t < fuel →
      (∀ k ∈ wordT n s par gl fuel q[t]!, k < m) ∧ walkT adj (wordT n s par gl fuel q[t]!) s = q[t]!
  | t, ht, 0, hf => absurd hf (Nat.not_lt_zero _)
  | t, ht, fuel + 1, hf => by
    by_cases e : q[t]! = s
    · have hw : wordT n s par gl (fuel + 1) q[t]! = [] := by
        rw [wordT, ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.2 e))]
      rw [hw]
      exact ⟨fun k hk => absurd hk List.not_mem_nil, e.symm⟩
    · have tpos : 0 < t := by
        rcases Nat.eq_zero_or_pos t with rfl | h'
        · exact absurd I.q0 e
        · exact h'
      have yq := get_mem q ht
      have pne := (I.reach _ (I.qlt _ yq)).2 yq
      have hw : wordT n s par gl (fuel + 1) q[t]! =
          gl[q[t]!]! :: wordT n s par gl fuel par[q[t]!]! := by
        rw [wordT, ite_eq_right_of_eq_false _ _ (eq_false fun h' => e (beq_iff_eq.1 h')),
          ite_eq_right_of_eq_false _ _ (eq_false fun h' => pne (beq_iff_eq.1 h'))]
      obtain ⟨t', ht't, e1, e2, e3⟩ := I.tree t ht tpos
      obtain ⟨ih1, ih2⟩ := word_ok I t' (by omega) fuel (by omega)
      rw [e1] at ih1 ih2
      rw [hw]
      refine ⟨fun k hk => ?_, ?_⟩
      · rcases List.mem_cons.1 hk with rfl | hk'
        · exact e2
        · exact ih1 k hk'
      · change (adj[gl[q[t]!]!]!)[walkT adj (wordT n s par gl fuel par[q[t]!]!) s]! = q[t]!
        rw [ih2, e3]

theorem bfs_word_sound {n m s fuel : ℕ} {adj : Array (Array ℕ)} (hs : s < n) (hfuel : n ≤ fuel)
    (hadj : ∀ k < m, ∀ x < n, (adj[k]!)[x]! < n) {j : ℕ} {w : List ℕ} (hw : ∀ k ∈ w, k < m)
    (hj : walkT adj w s = j) :
    (∀ k ∈ wordT n s (bfsT n m s adj).1 (bfsT n m s adj).2 fuel j, k < m) ∧
      walkT adj (wordT n s (bfsT n m s adj).1 (bfsT n m s adj).2 fuel j) s = j := by
  rw [bfsT_eq]
  dsimp only
  have I := outer_loop hadj n 0 (initS n s) (init_inv (m := m) (adj := adj) hs)
  rw [Nat.zero_add] at I
  generalize (List.range' 0 n).foldl (outer n m adj) (initS n s) = st at I ⊢
  obtain ⟨par, gl, q, h⟩ := st
  obtain ⟨inv, hle, closed, cnt⟩ := I
  dsimp only at inv hle closed cnt ⊢
  have hsz := size_le inv
  have hh : h = q.size := by omega
  have walk_mem : ∀ v : List ℕ, (∀ k ∈ v, k < m) → walkT adj v s ∈ q.toList := by
    intro v
    induction v with
    | nil =>
      intro _
      change s ∈ q.toList
      rw [← inv.q0]
      exact get_mem q inv.qpos
    | cons k v ih =>
      intro hv
      obtain ⟨t, ht, e⟩ := (mem_iff_get q _).1 (ih fun k' h' => hv k' (List.mem_cons_of_mem _ h'))
      change (adj[k]!)[walkT adj v s]! ∈ q.toList
      rw [← e]
      exact closed t (by omega) k (hv k List.mem_cons_self)
  obtain ⟨t, ht, e⟩ := (mem_iff_get q _).1 (walk_mem w hw)
  rw [← hj, ← e]
  exact word_ok inv t ht fuel (by omega)

end CFSG.KS.Bfs

end
