module

public import CFSG.Sporadic.Co2InvCheckInputs
public import Certificates.Data.Kernel.MonsterB.BfsReplay

public section

namespace CFSG.KC.Co2InvS

open CFSG.Sporadic.Co2Inv CFSG.Sporadic.SmallF2.Native CFSG.KC.Bfs

abbrev ISt := Array (Array Nat) × Array Nat × Array Nat × Std.HashMap (Array Nat) Nat × Array Nat

abbrev OSt :=
  Array (Array Nat) × Array Nat × Array Nat × Array (Array Nat) × Std.HashMap (Array Nat) Nat

@[expose] def inner (gens : Array (Array Nat)) (x : Array Nat) (h : Nat) (s : ISt) (j : Nat) :
    ISt :=
  match s.2.2.2.1.get? (mulRows 22 x gens[j]!) with
  | some i => (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.push i)
  | none => (s.1.push (mulRows 22 x gens[j]!), s.2.1.push h, s.2.2.1.push j,
      s.2.2.2.1.insert (mulRows 22 x gens[j]!) s.1.size, s.2.2.2.2.push s.1.size)

@[expose] def outer (gens : Array (Array Nat)) (s : OSt) (h : Nat) : OSt :=
  if h < s.1.size then
    (fun t : ISt => (t.1, t.2.1, t.2.2.1, s.2.2.2.1.push t.2.2.2.2, t.2.2.2.1))
      ((List.range gens.size).foldl (inner gens s.1[h]! h) (s.1, s.2.1, s.2.2.1, s.2.2.2.2, #[]))
  else s

@[expose] def init : OSt :=
  (#[idRows 22], #[0], #[0], #[], (∅ : Std.HashMap (Array Nat) Nat).insert (idRows 22) 0)

theorem forIn_id_eq_foldl {α β : Type} (l : List α) (b : β) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (hf : ∀ a b, f a b = ForInStep.yield (g b a)) :
    forIn l b f = l.foldl g b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, hf, List.foldl_cons]
    exact ih _

theorem bfsS_eq (gens : Array (Array Nat)) (cap : Nat) :
    bfsS gens cap = (fun s : OSt => (⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2⟩ : SEnum))
      ((List.range cap).foldl (outer gens) init) := by
  unfold bfsS
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  rw [forIn_id_eq_foldl (g := outer gens)]
  · rfl
  · intro h s
    unfold outer
    split
    · rw [forIn_id_eq_foldl (g := inner gens s.1[h]! h)]
      · rfl
      · intro j t
        unfold inner
        split <;> (rename_i heq; simp only [heq]; rfl)
    · rfl

section Replay

variable {gens : Array (Array Nat)} {N : Nat} {Lf : Nat → Array Nat} {Tf : Nat → Nat → Nat}

theorem push_get_lt {α : Type} [Inhabited α] (a : Array α) (x : α) {j : Nat} (h : j < a.size) :
    (a.push x)[j]! = a[j]! := by
  rw [getElem!_pos (a.push x) j (by rw [Array.size_push]; omega), getElem!_pos a j h,
    Array.getElem_push_lt h]

theorem push_get_size {α : Type} [Inhabited α] (a : Array α) (x : α) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]

structure Pre (gens : Array (Array Nat)) (Lf : Nat → Array Nat) (m : Nat) (el : Array (Array Nat))
    (par lab : Array Nat) (pos : Std.HashMap (Array Nat) Nat) : Prop where
  size : el.size = m
  elem : ∀ i < m, el[i]! = Lf i
  psize : par.size = m
  lsize : lab.size = m
  tree : ∀ i, 0 < i → i < m →
    par[i]! < i ∧ lab[i]! < gens.size ∧ el[i]! = mulRows 22 el[par[i]!]! gens[lab[i]!]!
  pos : ∀ x i, pos[x]? = some i ↔ i < m ∧ Lf i = x

@[expose] def RowsOK (gens : Array (Array Nat)) (Tf : Nat → Nat → Nat) (h : Nat)
    (tbl : Array (Array Nat)) : Prop :=
  tbl.size = h ∧ ∀ i < h, (tbl[i]!).size = gens.size ∧ ∀ j < gens.size, (tbl[i]!)[j]! = Tf i j

theorem rfold_none (k : Nat) : ∀ l : List Nat, l.foldl (rStep Tf k) none = none
  | [] => rfl
  | _ :: l => by rw [List.foldl_cons]; exact rfold_none k l

theorem rfold_le {k : Nat} : ∀ (l : List Nat) (a b : Nat),
    l.foldl (rStep Tf k) (some a) = some b → a ≤ b
  | [], a, b, e => by
    simp only [List.foldl_nil, Option.some.injEq] at e
    omega
  | x :: l, a, b, e => by
    rw [List.foldl_cons] at e
    simp only [rStep] at e
    split at e
    · exact rfold_le l _ _ e
    · split at e
      · exact Nat.le_trans (Nat.le_succ a) (rfold_le l _ _ e)
      · rw [rfold_none] at e
        cases e

theorem inner_spec (hinj : ∀ a < N, ∀ b < N, Lf a = Lf b → a = b)
    (hE : ∀ i < N, ∀ j < gens.size, Tf i j < N ∧ Lf (Tf i j) = mulRows 22 (Lf i) gens[j]!)
    {k : Nat} (hk : k < N) :
    ∀ n ≤ gens.size, ∀ (m m' : Nat) (s : ISt), k < m →
      Pre gens Lf m s.1 s.2.1 s.2.2.1 s.2.2.2.1 → s.2.2.2.2 = #[] →
      (List.range n).foldl (rStep Tf k) (some m) = some m' →
      Pre gens Lf m' ((List.range n).foldl (inner gens (Lf k) k) s).1
        ((List.range n).foldl (inner gens (Lf k) k) s).2.1
        ((List.range n).foldl (inner gens (Lf k) k) s).2.2.1
        ((List.range n).foldl (inner gens (Lf k) k) s).2.2.2.1 ∧
      (((List.range n).foldl (inner gens (Lf k) k) s).2.2.2.2).size = n ∧
      ∀ j < n, (((List.range n).foldl (inner gens (Lf k) k) s).2.2.2.2)[j]! = Tf k j := by
  intro n
  induction n with
  | zero =>
    intro _ m m' s _ hp hr h
    simp only [List.range_zero, List.foldl_nil, Option.some.injEq] at h ⊢
    subst h
    rw [hr]
    exact ⟨hp, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hn m m' s hkm hp hr h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h ⊢
    cases ho : (List.range n).foldl (rStep Tf k) (some m) with
    | none =>
      rw [ho] at h
      simp [rStep] at h
    | some m₁ =>
      rw [ho] at h
      obtain ⟨hp₁, hs₁, hr₁⟩ := ih (by omega) m m₁ s hkm hp hr ho
      have hm₁ : m ≤ m₁ := rfold_le _ _ _ ho
      generalize (List.range n).foldl (inner gens (Lf k) k) s = t at hp₁ hs₁ hr₁
      obtain ⟨el, par, lab, pos, row⟩ := t
      dsimp only at hp₁ hs₁ hr₁ ⊢
      obtain ⟨hTlt, hTe⟩ := hE k hk n (by omega)
      have hx : el[k]! = Lf k := hp₁.elem k (by omega)
      simp only [rStep] at h
      unfold inner
      dsimp only
      rw [Std.HashMap.get?_eq_getElem?]
      split at h
      ·
        next hlt =>
        cases h
        have hget : pos[mulRows 22 (Lf k) gens[n]!]? = some (Tf k n) :=
          (hp₁.pos _ _).2 ⟨hlt, hTe⟩
        rw [hget]
        dsimp only
        refine ⟨hp₁, by rw [Array.size_push, hs₁], fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [push_get_lt _ _ (by omega)]
          exact hr₁ j hj
        · rw [← hs₁, push_get_size]
      · split at h
        ·
          next _ heq =>
          cases h
          have hnone : pos[mulRows 22 (Lf k) gens[n]!]? = none := by
            cases e : pos[mulRows 22 (Lf k) gens[n]!]? with
            | none => rfl
            | some i =>
              obtain ⟨hi, hie⟩ := (hp₁.pos _ _).1 e
              rw [← hTe, heq] at hie
              have := hinj i (by omega) m₁ (by omega) hie
              omega
          rw [hnone]
          dsimp only
          have hsz := hp₁.size
          have hget : ∀ i < m₁, (el.push (mulRows 22 (Lf k) gens[n]!))[i]! = el[i]! :=
            fun i hi => push_get_lt _ _ (by omega)
          refine ⟨⟨by rw [Array.size_push, hsz], fun i hi => ?_, by rw [Array.size_push,
            hp₁.psize], by rw [Array.size_push, hp₁.lsize], fun i h0 hi => ?_, fun x i => ?_⟩,
            by rw [Array.size_push, hs₁], fun j hj => ?_⟩
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
            · rw [hget i hi]
              exact hp₁.elem i hi
            · rw [← hsz, push_get_size, hsz, ← heq, hTe]
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
            · obtain ⟨h1, h2, h3⟩ := hp₁.tree i h0 hi
              rw [push_get_lt _ _ (by rw [hp₁.psize]; exact hi),
                push_get_lt _ _ (by rw [hp₁.lsize]; exact hi), hget i hi, hget _ (by omega)]
              exact ⟨h1, h2, h3⟩
            · rw [← hp₁.psize, push_get_size, hp₁.psize, ← hp₁.lsize, push_get_size,
                hp₁.lsize, ← hsz, push_get_size, hsz, hget k (by omega), hx]
              exact ⟨by omega, by omega, rfl⟩
          · rw [Std.HashMap.getElem?_insert]
            by_cases hy : mulRows 22 (Lf k) gens[n]! = x
            · simp only [beq_iff_eq, hy, ↓reduceIte]
              rw [hsz]
              constructor
              · intro e
                cases e
                refine ⟨by omega, ?_⟩
                rw [← hy, ← hTe, heq]
              · rintro ⟨hi, hie⟩
                rw [← hy, ← hTe, heq] at hie
                rw [hinj i (by omega) _ (by omega) hie]
            · simp only [beq_iff_eq, hy, ↓reduceIte]
              rw [hp₁.pos]
              constructor
              · rintro ⟨hi, hie⟩
                exact ⟨by omega, hie⟩
              · rintro ⟨hi, hie⟩
                rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
                · exact ⟨hi, hie⟩
                · exact absurd (by rw [← hie, ← heq, hTe]) hy
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
            · rw [push_get_lt _ _ (by omega)]
              exact hr₁ j hj
            · rw [← hs₁, push_get_size, hsz, hs₁, heq]
        · exact absurd h (by simp)

theorem outer_spec (hinj : ∀ a < N, ∀ b < N, Lf a = Lf b → a = b)
    (hE : ∀ i < N, ∀ j < gens.size, Tf i j < N ∧ Lf (Tf i j) = mulRows 22 (Lf i) gens[j]!)
    (h0 : Lf 0 = idRows 22) {M : Nat → Nat} (hM0 : M 0 = 1)
    (hM : ∀ k < N, k < M k ∧ rRow Tf gens.size k (M k) = some (M (k + 1))) :
    ∀ n ≤ N, Pre gens Lf (M n) ((List.range n).foldl (outer gens) init).1
        ((List.range n).foldl (outer gens) init).2.1
        ((List.range n).foldl (outer gens) init).2.2.1
        ((List.range n).foldl (outer gens) init).2.2.2.2 ∧
      RowsOK gens Tf n ((List.range n).foldl (outer gens) init).2.2.2.1 := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [hM0]
    refine ⟨⟨rfl, fun i hi => ?_, rfl, rfl, fun i h0' hi => absurd hi (by omega), fun x i => ?_⟩,
      rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · have : i = 0 := by omega
      subst this
      rw [h0]
      rfl
    · change ((∅ : Std.HashMap (Array Nat) Nat).insert (idRows 22) 0)[x]? = some i ↔ _
      rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
      by_cases hx : idRows 22 = x
      · simp only [beq_iff_eq, hx, ↓reduceIte]
        constructor
        · intro e
          cases e
          exact ⟨by omega, by rw [h0, hx]⟩
        · rintro ⟨hi, -⟩
          have : i = 0 := by omega
          rw [this]
      · simp only [beq_iff_eq, hx, ↓reduceIte]
        constructor
        · intro e
          cases e
        · rintro ⟨hi, hie⟩
          have : i = 0 := by omega
          subst this
          exact absurd (by rw [← hie, h0]) hx
  | succ n ih =>
    intro hn
    obtain ⟨hp, hr⟩ := ih (by omega)
    obtain ⟨hkM, hrow⟩ := hM n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (outer gens) init = s at hp hr
    obtain ⟨el, par, lab, tbl, pos⟩ := s
    dsimp only at hp hr ⊢
    unfold outer
    dsimp only
    have hlt : n < el.size := by rw [hp.size]; exact hkM
    simp only [hlt, ↓reduceIte]
    rw [hp.elem n hkM]
    obtain ⟨hp', hs', hr'⟩ := inner_spec hinj hE (by omega) gens.size le_rfl (M n) (M (n + 1))
      (el, par, lab, pos, #[]) hkM hp rfl hrow
    generalize (List.range gens.size).foldl (inner gens (Lf n) n) (el, par, lab, pos, #[]) = t
      at hp' hs' hr'
    obtain ⟨el', par', lab', pos', row⟩ := t
    dsimp only at hp' hs' hr' ⊢
    refine ⟨hp', by rw [Array.size_push, hr.1], fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [push_get_lt _ _ (by rw [hr.1]; exact hi)]
      exact hr.2 i hi
    · rw [← hr.1, push_get_size, hr.1]
      exact ⟨hs', hr'⟩

theorem bfsS_replay (hinj : ∀ a < N, ∀ b < N, Lf a = Lf b → a = b)
    (hE : ∀ i < N, ∀ j < gens.size, Tf i j < N ∧ Lf (Tf i j) = mulRows 22 (Lf i) gens[j]!)
    (h0 : Lf 0 = idRows 22) {M : Nat → Nat} (hM0 : M 0 = 1) (hMN : M N = N)
    (hM : ∀ k < N, k < M k ∧ rRow Tf gens.size k (M k) = some (M (k + 1))) :
    (bfsS gens N).elems.size = N ∧ (∀ k < N, (bfsS gens N).elems[k]! = Lf k) ∧
      (∀ k, 0 < k → k < N → (bfsS gens N).par[k]! < k ∧ (bfsS gens N).lab[k]! < gens.size ∧
        (bfsS gens N).elems[k]! =
          mulRows 22 (bfsS gens N).elems[(bfsS gens N).par[k]!]! gens[(bfsS gens N).lab[k]!]!) ∧
      (∀ k < N, ∀ j < gens.size, ((bfsS gens N).tbl[k]!)[j]! = Tf k j) ∧
      (∀ x i, (bfsS gens N).pos[x]? = some i ↔ i < N ∧ Lf i = x) := by
  obtain ⟨hp, hr⟩ := outer_spec hinj hE h0 hM0 hM N le_rfl
  rw [hMN] at hp
  rw [bfsS_eq]
  exact ⟨hp.size, hp.elem, hp.tree, fun k hk j hj => (hr.2 k hk).2 j hj, hp.pos⟩

end Replay

end CFSG.KC.Co2InvS

end
