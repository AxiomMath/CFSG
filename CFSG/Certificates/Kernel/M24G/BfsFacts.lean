module

public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

def loopG {β : Type} (c : β → Prop) [DecidablePred c] (F : β → β) : Nat → β → β
  | 0, b => b
  | n + 1, b => if c b then loopG c F n (F b) else b

theorem forIn_yield {β γ : Type} (g : β → γ → β) (f : γ → β → Id (ForInStep β))
    (hf : ∀ a b, f a b = pure (.yield (g b a))) :
    ∀ (l : List γ) (init : β), forIn l init f = pure (l.foldl g init)
  | [], _ => rfl
  | a :: l, init => by
    rw [List.forIn_cons, hf, List.foldl_cons]
    exact forIn_yield g f hf l (g init a)

theorem forIn_range'_loop {β : Type} (c : β → Prop) [DecidablePred c] (F : β → β)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ a b, f a b = if c b then pure (.yield (F b)) else pure (.done b)) :
    ∀ (n a : Nat) (init : β), forIn (List.range' a n) init f = pure (loopG c F n init)
  | 0, _, _ => rfl
  | n + 1, a, init => by
    rw [List.range'_succ, List.forIn_cons, hf]
    by_cases h : c init
    · rw [if_pos h]
      change forIn (List.range' (a + 1) n) (F init) f = _
      rw [forIn_range'_loop c F f hf n (a + 1) (F init)]
      simp only [loopG, if_pos h]
    · rw [if_neg h]
      simp only [loopG, if_neg h]
      rfl

theorem loopG_stop {β : Type} {c : β → Prop} [DecidablePred c] {F : β → β} {b : β} (h : ¬ c b) :
    ∀ n, loopG c F n b = b
  | 0 => rfl
  | _ + 1 => by simp only [loopG, if_neg h]

theorem loopG_add {β : Type} (c : β → Prop) [DecidablePred c] (F : β → β) :
    ∀ (a d : Nat) (b : β), loopG c F (a + d) b = loopG c F d (loopG c F a b)
  | 0, d, b => by simp only [Nat.zero_add, loopG]
  | a + 1, d, b => by
    rw [Nat.add_right_comm]
    by_cases h : c b
    · simp only [loopG, if_pos h]
      exact loopG_add c F a d (F b)
    · simp only [loopG, if_neg h]
      exact (loopG_stop h d).symm

theorem loopG_inv {β : Type} {c : β → Prop} [DecidablePred c] {F : β → β} (P : β → Prop)
    (hF : ∀ b, c b → P b → P (F b)) : ∀ n b, P b → P (loopG c F n b)
  | 0, _, h => h
  | n + 1, b, h => by
    simp only [loopG]
    split
    · exact loopG_inv P hF n _ (hF b ‹_› h)
    · exact h

variable {α : Type} [Inhabited α]

abbrev BSt (α : Type) := Array α × Array Nat × Array Nat × Std.HashMap Nat Nat × Nat

def bfsAdd (key : α → Nat) (x : α) (h : Nat) (st : BSt α) (s : α → α) : BSt α :=
  if (!st.2.2.2.1.contains (key (s x))) = true then
    (st.1.push (s x), st.2.1.push h, st.2.2.1.push st.2.2.2.2,
      st.2.2.2.1.insert (key (s x)) st.1.size, st.2.2.2.2 + 1)
  else (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2 + 1)

def bfsHead (key : α → Nat) (steps : List (α → α)) (st : BSt α) : BSt α :=
  let r := steps.foldl (bfsAdd key st.1[st.2.2.2.2]! st.2.2.2.2)
    (st.1, st.2.1, st.2.2.1, st.2.2.2.1, 0)
  (r.1, r.2.1, r.2.2.1, r.2.2.2.1, st.2.2.2.2 + 1)

@[expose] def bfsGo (st : BSt α) : Prop := st.2.2.2.2 < st.1.size

instance : DecidablePred (bfsGo (α := α)) := fun st => Nat.decLt st.2.2.2.2 st.1.size

def bfsInit (key : α → Nat) (base : α) : BSt α :=
  (#[base], #[0], #[0], (∅ : Std.HashMap Nat Nat).insert (key base) 0, 0)

theorem bfs_eq_loop (key : α → Nat) (steps : List (α → α)) (base : α) (fuel : Nat) :
    Native.bfs key steps base fuel =
      ((loopG bfsGo (bfsHead key steps) fuel (bfsInit key base)).1,
        (loopG bfsGo (bfsHead key steps) fuel (bfsInit key base)).2.1,
        (loopG bfsGo (bfsHead key steps) fuel (bfsInit key base)).2.2.1) := by
  unfold Native.bfs
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : ([:fuel] : Std.Legacy.Range).size = fuel := by simp [Std.Legacy.Range.size]
  rw [hs]
  rw [forIn_range'_loop bfsGo (bfsHead key steps) _ (fun a b => ?_)]
  · rfl
  · unfold bfsGo
    split
    · rw [forIn_yield (bfsAdd key b.1[b.2.2.2.2]! b.2.2.2.2) _ (fun s st => ?_)]
      · rfl
      · unfold bfsAdd
        split <;> rfl
    · rfl

theorem push_get! {β : Type} [Inhabited β] {a : Array β} {i : Nat} (y : β) (hi : i < a.size) :
    (a.push y)[i]! = a[i]! := by
  rw [getElem!_pos (a.push y) i (by simp; omega), getElem!_pos a i hi, Array.getElem_push_lt hi]

theorem push_get!_size {β : Type} [Inhabited β] (a : Array β) (y : β) : (a.push y)[a.size]! = y := by
  rw [getElem!_pos (a.push y) a.size (by simp), Array.getElem_push_eq]

def TreeInv (steps : List (α → α)) (base : α) (L : Array α) (P G : Array Nat) : Prop :=
  P.size = L.size ∧ G.size = L.size ∧ 0 < L.size ∧ L[0]! = base ∧
    ∀ j, 0 < j → j < L.size → P[j]! < j ∧ G[j]! < steps.length ∧
      (steps.getD G[j]! id) L[P[j]!]! = L[j]!

theorem fold_tree (key : α → Nat) (steps : List (α → α)) (base x : α) (h : Nat) :
    ∀ (ss : List (α → α)) (L : Array α) (P G : Array Nat) (S : Std.HashMap Nat Nat) (j : Nat),
      steps.drop j = ss → TreeInv steps base L P G → h < L.size → L[h]! = x →
      TreeInv steps base (ss.foldl (bfsAdd key x h) (L, P, G, S, j)).1
          (ss.foldl (bfsAdd key x h) (L, P, G, S, j)).2.1
          (ss.foldl (bfsAdd key x h) (L, P, G, S, j)).2.2.1 ∧
        L.toList <+: (ss.foldl (bfsAdd key x h) (L, P, G, S, j)).1.toList
  | [], _, _, _, _, _, _, ht, _, _ => ⟨ht, List.prefix_refl _⟩
  | s :: ss, L, P, G, S, j, hd, ht, hh, hx => by
    obtain ⟨hj, hjs, hdrop⟩ := drop_eq_cons' hd
    rw [List.foldl_cons]
    have hstep : steps.getD j id = s := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hjs]
      rfl
    unfold bfsAdd
    dsimp only
    obtain ⟨t1, t2, t3, t4, t5⟩ := ht
    split
    · have ht' : TreeInv steps base (L.push (s x)) (P.push h) (G.push j) := by
        refine ⟨by simp [t1], by simp [t2], by simp, ?_, fun i hi1 hi2 => ?_⟩
        · rw [push_get! _ t3, t4]
        · simp only [Array.size_push] at hi2
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi2 with hi2 | rfl
          · obtain ⟨u1, u2, u3⟩ := t5 i hi1 hi2
            have e1 : (P.push h)[i]! = P[i]! := push_get! h (by omega)
            have e2 : (G.push j)[i]! = G[i]! := push_get! j (by omega)
            have e3 : (L.push (s x))[i]! = L[i]! := push_get! (s x) hi2
            have e4 : (L.push (s x))[P[i]!]! = L[P[i]!]! := push_get! (s x) (by omega)
            rw [e1, e2, e3, e4]
            exact ⟨u1, u2, u3⟩
          · have f1 : (P.push h)[L.size]! = h := by
              rw [← t1]
              exact push_get!_size P h
            have f2 : (G.push j)[L.size]! = j := by
              rw [← t2]
              exact push_get!_size G j
            have f3 : (L.push (s x))[L.size]! = s x := push_get!_size L (s x)
            have f4 : (L.push (s x))[h]! = x := by rw [push_get! _ hh, hx]
            rw [f1, f2, f3, f4, hstep]
            exact ⟨hh, hj, rfl⟩
      obtain ⟨r1, r2⟩ := fold_tree key steps base x h ss _ _ _ _ _ hdrop ht' (by simp; omega)
        (by rw [push_get! _ hh, hx])
      refine ⟨r1, List.IsPrefix.trans ?_ r2⟩
      simp
    · exact fold_tree key steps base x h ss _ _ _ _ _ hdrop ⟨t1, t2, t3, t4, t5⟩ hh hx
where
  drop_eq_cons' {l : List (α → α)} {n : Nat} {y : α → α} {t : List (α → α)}
      (e : l.drop n = y :: t) : ∃ hn : n < l.length, l[n] = y ∧ l.drop (n + 1) = t := by
    have hn : n < l.length := by
      refine Nat.lt_of_not_le fun h => ?_
      rw [List.drop_eq_nil_of_le h] at e
      cases e
    rw [List.drop_eq_getElem_cons hn] at e
    injection e with e1 e2
    exact ⟨hn, e1, e2⟩

theorem head_tree (key : α → Nat) (steps : List (α → α)) (base : α) (st : BSt α)
    (hg : bfsGo st) (ht : TreeInv steps base st.1 st.2.1 st.2.2.1) :
    TreeInv steps base (bfsHead key steps st).1 (bfsHead key steps st).2.1
        (bfsHead key steps st).2.2.1 ∧
      st.1.toList <+: (bfsHead key steps st).1.toList :=
  fold_tree key steps base _ _ steps st.1 st.2.1 st.2.2.1 st.2.2.2.1 0 rfl ht hg rfl

theorem bfs_tree (key : α → Nat) (steps : List (α → α)) (base : α) (fuel : Nat) :
    TreeInv steps base (Native.bfs key steps base fuel).1 (Native.bfs key steps base fuel).2.1
      (Native.bfs key steps base fuel).2.2 := by
  rw [bfs_eq_loop]
  refine loopG_inv (fun st => TreeInv steps base st.1 st.2.1 st.2.2.1)
    (fun st hg ht => (head_tree key steps base st hg ht).1) fuel _ ?_
  refine ⟨rfl, rfl, Nat.one_pos, rfl, fun j h1 h2 => ?_⟩
  change j < 1 at h2
  omega

theorem fold_prefix (key : α → Nat) (x : α) (h : Nat) :
    ∀ (ss : List (α → α)) (st : BSt α), st.1.toList <+: (ss.foldl (bfsAdd key x h) st).1.toList
  | [], _ => List.prefix_refl _
  | s :: ss, st => by
    rw [List.foldl_cons]
    refine List.IsPrefix.trans ?_ (fold_prefix key x h ss _)
    unfold bfsAdd
    split
    · simp
    · exact List.prefix_refl _

theorem head_prefix (key : α → Nat) (steps : List (α → α)) (b : BSt α) :
    b.1.toList <+: (bfsHead key steps b).1.toList :=
  fold_prefix key _ _ steps (b.1, b.2.1, b.2.2.1, b.2.2.2.1, 0)

theorem bfs_prefix (key : α → Nat) (steps : List (α → α)) (base : α) {f f' : Nat} (hf : f ≤ f') :
    (Native.bfs key steps base f).1.toList <+: (Native.bfs key steps base f').1.toList := by
  rw [bfs_eq_loop, bfs_eq_loop]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hf
  dsimp only
  rw [loopG_add]
  generalize loopG bfsGo (bfsHead key steps) f (bfsInit key base) = st
  exact loopG_inv (c := bfsGo) (F := bfsHead key steps)
    (fun st' => st.1.toList <+: st'.1.toList)
    (fun b _ hb => hb.trans (head_prefix key steps b)) d st (List.prefix_refl _)

theorem reachOK_of_tree {steps : List (Nat → Nat)} {n p : Nat} {c : List Nat}
    (hlt : ∀ j < (Native.bfs (fun i => i) steps p 5000).1.size,
      (Native.bfs (fun i => i) steps p 5000).1[j]! < n)
    (hc : ∀ q ∈ c, q ∈ (Native.bfs (fun i => i) steps p 5000).1.toList) :
    Native.reachOK n steps p c = true := by
  obtain ⟨t1, t2, t3, t4, t5⟩ := bfs_tree (fun i => i) steps p 5000
  unfold Native.reachOK
  generalize Native.bfs (fun i => i) steps p 5000 = r at t1 t2 t3 t4 t5 hc hlt
  obtain ⟨L, P, G⟩ := r
  dsimp only at t1 t2 t3 t4 t5 hc hlt ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, t1, t2, t3, t4, and_self,
    true_and, Native.allLt, List.all_eq_true, List.mem_range, Bool.or_eq_true]
  refine ⟨fun j hj => ⟨hlt j hj, ?_⟩, fun q hq => ?_⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact Or.inl rfl
    · obtain ⟨u1, u2, u3⟩ := t5 j hj0 hj
      exact Or.inr ⟨⟨u1, u2⟩, u3⟩
  · exact Array.contains_eq_true_of_mem (Array.mem_toList_iff.1 (hc q hq))

theorem reachOK_of_closed {steps : List (Nat → Nat)} {n p : Nat} (hp : p < n)
    (hcl : ∀ s ∈ steps, ∀ i < n, s i < n) {c : List Nat}
    (hc : ∀ q ∈ c, q ∈ (Native.bfs (fun i => i) steps p 5000).1.toList) :
    Native.reachOK n steps p c = true := by
  refine reachOK_of_tree ?_ hc
  obtain ⟨t1, t2, t3, t4, t5⟩ := bfs_tree (fun i => i) steps p 5000
  generalize Native.bfs (fun i => i) steps p 5000 = r at t1 t2 t3 t4 t5 ⊢
  obtain ⟨L, P, G⟩ := r
  dsimp only at t1 t2 t3 t4 t5 ⊢
  have hlt' : ∀ m, ∀ j < m, j < L.size → L[j]! < n := by
    intro m
    induction m with
    | zero => intro j hj; omega
    | succ m ih =>
      intro j hjm hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [t4]
        exact hp
      · obtain ⟨u1, u2, u3⟩ := t5 j hj0 hj
        rw [← u3]
        have hs : steps.getD G[j]! id ∈ steps := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem u2]
          exact List.getElem_mem u2
        exact hcl _ hs _ (ih _ (by omega) (by omega))
  exact fun j hj => hlt' (j + 1) j (by omega) hj

end CFSG.KC.M24G
