module

public import CFSG.Sporadic.Schreier.J1ClosureSpec

public section

namespace CFSG.KS.KeyBfs

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def LexLt (a b c d : Nat) : Prop := a < c ∨ (a = c ∧ b < d)

structure KReplay (n : Nat) (st : Nat → Table → Table) (k : Nat) (root : Table) (cnt : Nat)
    (T : Nat → Table) (par lab : Nat → Nat) (pos : Nat → Nat → Nat) : Prop where
  pos_cnt : 0 < cnt
  root_eq : T 0 = root
  par_zero : par 0 = 0
  lab_zero : lab 0 = 0
  inj : ∀ a < cnt, ∀ b < cnt, key n (T a) = key n (T b) → a = b
  tree : ∀ i, 0 < i → i < cnt → par i < i ∧ lab i < k ∧ T i = st (lab i) (T (par i))
  order : ∀ i, 0 < i → i + 1 < cnt → LexLt (par i) (lab i) (par (i + 1)) (lab (i + 1))
  close : ∀ h < cnt, ∀ j < k, pos h j < cnt ∧ st j (T h) = T (pos h j) ∧
    (pos h j = 0 ∨ ¬ LexLt h j (par (pos h j)) (lab (pos h j)))

theorem forIn_range'_done {β : Type} (n s : Nat) (init : β) (f : Nat → β → Id (ForInStep β))
    (P : Nat → β → Prop) (Q : β → Prop)
    (h : ∀ j < n, ∀ b, P j b → (∃ b', f (s + j) b = pure (ForInStep.yield b') ∧ P (j + 1) b') ∨
      (∃ b', f (s + j) b = pure (ForInStep.done b') ∧ Q b'))
    (hn : ∀ b, P n b → Q b) (h0 : P 0 init) : Q (Id.run (forIn (List.range' s n) init f)) := by
  induction n generalizing s init P with
  | zero => simpa using hn init h0
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    rcases h 0 (by omega) init h0 with ⟨b', hb, hP⟩ | ⟨b', hb, hQ⟩
    · rw [Nat.add_zero] at hb
      rw [hb]
      have := ih (s + 1) b' (fun j b => P (j + 1) b) (fun j hj b hbj => by
        rcases h (j + 1) (by omega) b hbj with ⟨b'', e, p⟩ | ⟨b'', e, q⟩
        · exact Or.inl ⟨b'', by rw [show s + 1 + j = s + (j + 1) by omega]; exact e, p⟩
        · exact Or.inr ⟨b'', by rw [show s + 1 + j = s + (j + 1) by omega]; exact e, q⟩)
        (fun b hb => hn b hb) hP
      simpa using this
    · rw [Nat.add_zero] at hb
      rw [hb]
      simpa using hQ

theorem forIn_range'_yield {β : Type} (n s : Nat) (init : β) (f : Nat → β → Id (ForInStep β))
    (P : Nat → β → Prop)
    (h : ∀ j < n, ∀ b, P j b → ∃ b', f (s + j) b = pure (ForInStep.yield b') ∧ P (j + 1) b')
    (h0 : P 0 init) : P n (Id.run (forIn (List.range' s n) init f)) :=
  forIn_range'_done n s init f P (P n) (fun j hj b hb => Or.inl (h j hj b hb)) (fun _ hb => hb) h0

theorem push_lt {α : Type} [Inhabited α] {a : Array α} {x : α} {i : Nat} (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), Array.getElem_push_lt h, getElem!_pos a i h]

theorem push_eq {α : Type} [Inhabited α] {a : Array α} {x : α} : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

abbrev St := Std.HashSet Nat × Array Table × Array Nat × Array Nat

@[expose] def innerBody (n : Nat) (st : Nat → Table → Table) (t : Table) (h j : Nat) (s : St) :
    Id (ForInStep St) :=
  if (!s.1.contains (key n (st j t))) = true then
    pure (ForInStep.yield (s.1.insert (key n (st j t)), s.2.1.push (st j t), s.2.2.1.push h,
      s.2.2.2.push j))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def outerBody (n : Nat) (st : Nat → Table → Table) (k h : Nat) (s : St) :
    Id (ForInStep St) :=
  if h < s.2.1.size then
    pure (ForInStep.yield (Id.run (forIn (List.range' 0 k) (s.1, s.2.1, s.2.2.1, s.2.2.2)
      (innerBody n st s.2.1[h]! h))))
  else pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def initSt (n : Nat) (root : Table) : St :=
  ((∅ : Std.HashSet Nat).insert (key n root), #[root], #[0], #[0])

@[expose] def keyBfs (n : Nat) (st : Nat → Table → Table) (k : Nat) (root : Table) (cap : Nat) :
    Array Table × Array Nat × Array Nat :=
  let s := Id.run (forIn (List.range' 0 cap) (initSt n root) (outerBody n st k))
  (s.2.1, s.2.2.1, s.2.2.2)

theorem conjClosure_eq (n : Nat) (gens gensInv : Array Table) (x : Table) (cap : Nat) :
    conjClosure n gens gensInv x cap =
      keyBfs n (fun l y => conjT n gens[l]! gensInv[l]! y) gens.size x cap := by
  unfold conjClosure keyBfs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem mulClosure_eq (n : Nat) (gens : Array Table) (cap : Nat) :
    CFSG.Sporadic.Schreier.mulClosure n gens cap =
      keyBfs n (fun l y => compT n y gens[l]!) gens.size (idT n) cap := by
  unfold CFSG.Sporadic.Schreier.mulClosure keyBfs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

@[expose] def Inv (n cnt : Nat) (T : Nat → Table) (par lab : Nat → Nat) (h j : Nat) (s : St) :
    Prop :=
  s.2.1.size ≤ cnt ∧ s.2.2.1.size = s.2.1.size ∧ s.2.2.2.size = s.2.1.size ∧
    (∀ i < s.2.1.size, s.2.1[i]! = T i ∧ s.2.2.1[i]! = par i ∧ s.2.2.2[i]! = lab i) ∧
    (∀ x, s.1.contains x = true ↔ ∃ i < s.2.1.size, key n (T i) = x) ∧
    (∀ i < cnt, i < s.2.1.size ↔ (i = 0 ∨ LexLt (par i) (lab i) h j))

section

variable {n : Nat} {st : Nat → Table → Table} {k : Nat} {root : Table} {cnt : Nat}
  {T : Nat → Table} {par lab : Nat → Nat} {pos : Nat → Nat → Nat}

theorem lex_trans {a b c d e f : Nat} (h1 : LexLt a b c d) (h2 : LexLt c d e f) : LexLt a b e f := by
  unfold LexLt at *
  omega

theorem lex_irrefl {a b : Nat} : ¬ LexLt a b a b := by
  unfold LexLt
  omega

theorem order_lt (R : KReplay n st k root cnt T par lab pos) {i i' : Nat} (h0 : 0 < i)
    (hi : i < i') (hi' : i' < cnt) : LexLt (par i) (lab i) (par i') (lab i') := by
  induction i' with
  | zero => omega
  | succ i' ih =>
    rcases Nat.lt_or_ge i i' with a | a
    · exact lex_trans (ih a (by omega)) (R.order i' (by omega) hi')
    · have e : i = i' := by omega
      subst e
      exact R.order i h0 hi'

theorem inv_init (R : KReplay n st k root cnt T par lab pos) :
    Inv n cnt T par lab 0 0 (initSt n root) := by
  refine ⟨by simp [initSt]; exact R.pos_cnt, rfl, rfl, fun i hi => ?_, fun x => ?_,
    fun i hi => ?_⟩
  · have : i = 0 := by simp [initSt] at hi; omega
    subst this
    simp [initSt, R.root_eq, R.par_zero, R.lab_zero]
  · simp only [initSt]
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
    constructor
    · intro e
      exact ⟨0, by simp, by rw [R.root_eq]; exact beq_iff_eq.1 e⟩
    · rintro ⟨i, hi, e⟩
      have : i = 0 := by simp at hi; omega
      subst this
      rw [← e, R.root_eq]
      exact beq_self_eq_true _
  · simp only [initSt, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
    unfold LexLt
    constructor
    · intro h
      exact Or.inl (by omega)
    · rintro (e | e)
      · omega
      · omega

theorem inner_step (R : KReplay n st k root cnt T par lab pos) {h j : Nat} (hh : h < cnt)
    (hj : j < k) {s : St} (hI : Inv n cnt T par lab h j s) :
    ∃ s', innerBody n st (T h) h j s = pure (ForInStep.yield s') ∧
      Inv n cnt T par lab h (j + 1) s' ∧ s.2.1.size ≤ s'.2.1.size := by
  obtain ⟨hle, hp, hl, hget, hK, hch⟩ := hI
  obtain ⟨hq, hx, hor⟩ := R.close h hh j hj
  generalize hqdef : pos h j = q at hq hx hor
  have hmove : ∀ i < cnt, (i = 0 ∨ LexLt (par i) (lab i) h (j + 1)) ↔
      ((i = 0 ∨ LexLt (par i) (lab i) h j) ∨ (0 < i ∧ par i = h ∧ lab i = j)) := by
    intro i _
    unfold LexLt
    omega
  by_cases hnew : 0 < q ∧ par q = h ∧ lab q = j
  ·
    obtain ⟨hq0, hpq, hlq⟩ := hnew
    have hqs : ¬ q < s.2.1.size := by
      rw [hch q hq]
      rintro (e | e)
      · omega
      · rw [hpq, hlq] at e
        exact lex_irrefl e
    have hqm : q = s.2.1.size := by
      refine Nat.le_antisymm (Nat.le_of_not_lt fun hlt => ?_) (by omega)
      have hm0 : 0 < s.2.1.size := by
        have := (hch 0 R.pos_cnt).2 (Or.inl rfl)
        omega
      have hns : ¬ (s.2.1.size = 0 ∨ LexLt (par s.2.1.size) (lab s.2.1.size) h j) := by
        rw [← hch s.2.1.size (by omega)]
        exact Nat.lt_irrefl _
      have := order_lt R hm0 hlt hq
      rw [hpq, hlq] at this
      unfold LexLt at this hns
      omega
    have hnc : s.1.contains (key n (st j (T h))) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      obtain ⟨i, hi, e⟩ := (hK _).1 hc
      rw [hx] at e
      have := R.inj i (by omega) q hq e
      omega
    refine ⟨(s.1.insert (key n (st j (T h))), s.2.1.push (st j (T h)), s.2.2.1.push h,
      s.2.2.2.push j), by simp [innerBody, hnc], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp⟩
    · simp only [Array.size_push]
      omega
    · simp [hp]
    · simp [hl]
    · intro i hi
      simp only [Array.size_push] at hi
      rcases Nat.lt_or_ge i s.2.1.size with a | a
      · rw [push_lt a, push_lt (by omega : i < s.2.2.1.size),
          push_lt (by omega : i < s.2.2.2.size)]
        exact hget i a
      · have e : i = s.2.1.size := by omega
        subst e
        have e1 : (s.2.2.1.push h)[s.2.1.size]! = h := by rw [← hp]; exact push_eq
        have e2 : (s.2.2.2.push j)[s.2.1.size]! = j := by rw [← hl]; exact push_eq
        refine ⟨?_, ?_, ?_⟩
        · change (s.2.1.push (st j (T h)))[s.2.1.size]! = T s.2.1.size
          rw [push_eq, ← hqm, hx]
        · change (s.2.2.1.push h)[s.2.1.size]! = par s.2.1.size
          rw [e1, ← hqm, hpq]
        · change (s.2.2.2.push j)[s.2.1.size]! = lab s.2.1.size
          rw [e2, ← hqm, hlq]
    · intro y
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hK]
      simp only [Array.size_push]
      constructor
      · rintro (e | ⟨i, hi, e⟩)
        · exact ⟨s.2.1.size, by omega, by rw [← hqm, ← hx, e]⟩
        · exact ⟨i, by omega, e⟩
      · rintro ⟨i, hi, e⟩
        rcases Nat.lt_or_ge i s.2.1.size with a | a
        · exact Or.inr ⟨i, a, e⟩
        · have e' : i = s.2.1.size := by omega
          subst e'
          rw [← hqm, ← hx] at e
          exact Or.inl e
    · intro i hi
      simp only [Array.size_push]
      rw [hmove i hi, ← hch i hi]
      constructor
      · intro hlt
        rcases Nat.lt_or_ge i s.2.1.size with a | a
        · exact Or.inl a
        · have e : i = s.2.1.size := by omega
          subst e
          exact Or.inr ⟨by omega, by rw [← hqm]; exact hpq, by rw [← hqm]; exact hlq⟩
      · rintro (a | ⟨a0, a1, a2⟩)
        · omega
        · refine Classical.byContradiction fun hne => ?_
          have hgt : q < i := by omega
          have := order_lt R hq0 hgt hi
          rw [hpq, hlq, a1, a2] at this
          exact lex_irrefl this
  ·
    have hqs : q < s.2.1.size := by
      rw [hch q hq]
      rcases hor with e | e
      · exact Or.inl e
      · by_cases h0 : q = 0
        · exact Or.inl h0
        · right
          unfold LexLt at e ⊢
          have : ¬ (par q = h ∧ lab q = j) := fun e' => hnew ⟨by omega, e'.1, e'.2⟩
          omega
    have hc : s.1.contains (key n (st j (T h))) = true := (hK _).2 ⟨q, hqs, by rw [hx]⟩
    refine ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), by simp [innerBody, hc],
      ⟨hle, hp, hl, hget, hK, fun i hi => ?_⟩, Nat.le_refl _⟩
    rw [hmove i hi, ← hch i hi]
    constructor
    · exact Or.inl
    · rintro (a | ⟨a0, a1, a2⟩)
      · exact a
      · exfalso
        have e : key n (T i) = key n (T q) := by
          rw [← hx, (R.tree i a0 hi).2.2, a1, a2]
        have := R.inj i hi q hq e
        subst this
        exact hnew ⟨a0, a1, a2⟩

theorem inner_spec (R : KReplay n st k root cnt T par lab pos) {h : Nat} (hh : h < cnt) {s : St}
    (hI : Inv n cnt T par lab h 0 s) (hhs : h < s.2.1.size) :
    Inv n cnt T par lab (h + 1) 0
      (Id.run (forIn (List.range' 0 k) (s.1, s.2.1, s.2.2.1, s.2.2.2)
        (innerBody n st s.2.1[h]! h))) := by
  have hT : s.2.1[h]! = T h := (hI.2.2.2.1 h hhs).1
  rw [hT]
  have := forIn_range'_yield k 0 (s.1, s.2.1, s.2.2.1, s.2.2.2) (innerBody n st (T h) h)
    (fun j s' => Inv n cnt T par lab h j s' ∧ s.2.1.size ≤ s'.2.1.size)
    (fun j hj s' hP => by
      rw [Nat.zero_add]
      obtain ⟨s'', e, hI', hle⟩ := inner_step R hh hj hP.1
      exact ⟨s'', e, hI', by omega⟩)
    ⟨hI, Nat.le_refl _⟩
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, -⟩ := this
  refine ⟨a1, a2, a3, a4, a5, fun i hi => ?_⟩
  rw [a6 i hi]
  have hlab : 0 < i → lab i < k := fun h0 => (R.tree i h0 hi).2.1
  unfold LexLt
  constructor
  · rintro (e | e)
    · exact Or.inl e
    · right
      omega
  · rintro (e | e)
    · exact Or.inl e
    · by_cases h0 : i = 0
      · exact Or.inl h0
      · right
        have := hlab (by omega)
        omega

theorem outer_spec (R : KReplay n st k root cnt T par lab pos) {cap : Nat} (hcap : cnt ≤ cap) :
    Inv n cnt T par lab cnt 0
      (Id.run (forIn (List.range' 0 cap) (initSt n root) (outerBody n st k))) := by
  refine forIn_range'_done cap 0 (initSt n root) (outerBody n st k)
    (fun h s => h ≤ cnt ∧ Inv n cnt T par lab h 0 s) (Inv n cnt T par lab cnt 0)
    (fun h hh s hP => ?_) (fun s hP => ?_) ⟨Nat.zero_le _, inv_init R⟩
  · obtain ⟨hhc, hI⟩ := hP
    rw [Nat.zero_add]
    rcases Nat.lt_or_ge h cnt with a | a
    · have hhs : h < s.2.1.size := by
        rw [hI.2.2.2.2.2 h a]
        by_cases h0 : h = 0
        · exact Or.inl h0
        · right
          left
          exact (R.tree h (by omega) a).1
      exact Or.inl ⟨_, by simp [outerBody, hhs], by omega, inner_spec R a hI hhs⟩
    · have e : h = cnt := by omega
      subst e
      have hns : ¬ h < s.2.1.size := by have := hI.1; omega
      exact Or.inr ⟨_, by simp [outerBody, hns], hI⟩
  · have e : cap = cnt ∨ cnt < cap := by omega
    rcases e with e | e
    · have h2 := hP.2
      rw [e] at h2
      exact h2
    · exact absurd hP.1 (by omega)

end

theorem keyBfs_replay {n : Nat} {st : Nat → Table → Table} {k : Nat} {root : Table}
    {cnt cap : Nat} {T : Nat → Table} {par lab : Nat → Nat} {pos : Nat → Nat → Nat}
    (R : KReplay n st k root cnt T par lab pos) (hcap : cnt ≤ cap) :
    keyBfs n st k root cap = (Array.ofFn (n := cnt) fun i => T i.val,
      Array.ofFn (n := cnt) fun i => par i.val, Array.ofFn (n := cnt) fun i => lab i.val) := by
  have hO := outer_spec R hcap (st := st)
  unfold keyBfs
  generalize Id.run (forIn (List.range' 0 cap) (initSt n root) (outerBody n st k)) = s at hO
  obtain ⟨hle, hp, hl, hget, -, hch⟩ := hO
  have hsz : s.2.1.size = cnt := by
    have := (hch (cnt - 1) (by have := R.pos_cnt; omega)).2 (by
      by_cases h0 : cnt - 1 = 0
      · exact Or.inl h0
      · right
        left
        have := (R.tree (cnt - 1) (by omega) (by have := R.pos_cnt; omega)).1
        omega)
    omega
  have ext : ∀ {α : Type} [Inhabited α] (a : Array α) (f : Nat → α), a.size = cnt →
      (∀ i < cnt, a[i]! = f i) → a = Array.ofFn (n := cnt) fun i => f i.val :=
    fun a f ha hf => by
      apply Array.ext
      · simp [ha]
      · intro i h1 h2
        rw [Array.getElem_ofFn, ← getElem!_pos a i h1, hf i (by omega)]
  simp only
  rw [ext s.2.1 T hsz fun i hi => (hget i (by omega)).1,
    ext s.2.2.1 par (by omega) fun i hi => (hget i (by omega)).2.1,
    ext s.2.2.2 lab (by omega) fun i hi => (hget i (by omega)).2.2]

end CFSG.KS.KeyBfs

end
