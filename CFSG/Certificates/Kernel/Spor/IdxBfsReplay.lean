module

public import Std.Data.DTreeMap.Internal.Balancing

public section

namespace CFSG.KS.IdxBfs

@[expose] def idxBFS (N k : Nat) (nx : Nat → Nat → Nat) (r : Nat) :
    Array Nat × Array Nat × Array Nat := Id.run do
  let mut L : Array Nat := #[r]
  let mut par : Array Nat := #[0]
  let mut gen : Array Nat := #[0]
  let mut seen : Array Bool := (Array.replicate N false).set! r true
  for i in [0:N] do
    if i < L.size then
      for g in [0:k] do
        let m := nx L[i]! g
        if m < N && !seen[m]! then
          seen := seen.set! m true
          L := L.push m
          par := par.push i
          gen := gen.push g
  return (L, par, gen)

@[expose] def Lex (a b c d : Nat) : Prop := a < c ∨ (a = c ∧ b < d)

structure Facts (N k cnt : Nat) (nx : Nat → Nat → Nat) (T par lab : Nat → Nat)
    (pos : Nat → Nat → Nat) : Prop where
  pos_cnt : 0 < cnt
  cnt_le : cnt ≤ N
  lt_N : ∀ i < cnt, T i < N
  inj : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b
  par_zero : par 0 = 0
  lab_zero : lab 0 = 0
  tree : ∀ i, 0 < i → i < cnt → par i < i ∧ lab i < k ∧ nx (T (par i)) (lab i) = T i
  order : ∀ i, 0 < i → i + 1 < cnt → Lex (par i) (lab i) (par (i + 1)) (lab (i + 1))
  close : ∀ h < cnt, ∀ j < k, pos h j < cnt ∧ nx (T h) j = T (pos h j) ∧
    (pos h j = 0 ∨ ¬ Lex h j (par (pos h j)) (lab (pos h j)))

section Facts

variable {N k cnt : Nat} {nx : Nat → Nat → Nat} {T par lab : Nat → Nat} {pos : Nat → Nat → Nat}

theorem lex_trans {a b c d e f : Nat} (h1 : Lex a b c d) (h2 : Lex c d e f) : Lex a b e f := by
  unfold Lex at *
  omega

theorem lex_irrefl {a b : Nat} : ¬ Lex a b a b := by
  unfold Lex
  omega

theorem Facts.order_lt (F : Facts N k cnt nx T par lab pos) {i i' : Nat} (h0 : 0 < i)
    (hi : i < i') (hi' : i' < cnt) : Lex (par i) (lab i) (par i') (lab i') := by
  induction i' with
  | zero => omega
  | succ i' ih =>
    rcases Nat.lt_or_ge i i' with a | a
    · exact lex_trans (ih a (by omega)) (F.order i' (by omega) hi')
    · have e : i = i' := by omega
      subst e
      exact F.order i h0 hi'

end Facts

theorem forIn_range'_yield {β : Type} (n s : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) (P : Nat → β → Prop)
    (h : ∀ j < n, ∀ b, P j b → ∃ b', f (s + j) b = pure (ForInStep.yield b') ∧ P (j + 1) b')
    (h0 : P 0 init) : P n (Id.run (forIn (List.range' s n) init f)) := by
  induction n generalizing s init P with
  | zero => simpa using h0
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨b', hb, hP⟩ := h 0 (by omega) init h0
    rw [Nat.add_zero] at hb
    rw [hb]
    have := ih (s + 1) b' (fun j b => P (j + 1) b) (fun j hj b hbj => by
      obtain ⟨b'', e, p⟩ := h (j + 1) (by omega) b hbj
      exact ⟨b'', by rw [show s + 1 + j = s + (j + 1) by omega]; exact e, p⟩) hP
    simpa using this

theorem push_lt {α : Type} [Inhabited α] {a : Array α} {x : α} {i : Nat} (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), Array.getElem_push_lt h, getElem!_pos a i h]

theorem push_eq {α : Type} [Inhabited α] {a : Array α} {x : α} : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

theorem set_get {α : Type} [Inhabited α] {a : Array α} {y z : Nat} {v : α}
    (hz : z < a.size) : (a.set! y v)[z]! = if y = z then v else a[z]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (a.setIfInBounds y v) z (by simp; omega),
    Array.getElem_setIfInBounds hz, getElem!_pos a z hz]

abbrev St := Array Nat × Array Nat × Array Nat × Array Bool

@[expose] def innerB (N : Nat) (nx : Nat → Nat → Nat) (h g : Nat) (st : St) : Id (ForInStep St) :=
  if (decide (nx st.1[h]! g < N) && !st.2.2.2[nx st.1[h]! g]!) = true then
    pure (ForInStep.yield (st.1.push (nx st.1[h]! g), st.2.1.push h, st.2.2.1.push g,
      st.2.2.2.set! (nx st.1[h]! g) true))
  else pure (ForInStep.yield (st.1, st.2.1, st.2.2.1, st.2.2.2))

@[expose] def outerB (N k : Nat) (nx : Nat → Nat → Nat) (h : Nat) (st : St) : Id (ForInStep St) :=
  if h < st.1.size then
    pure (ForInStep.yield (Id.run (forIn (List.range' 0 k) (st.1, st.2.1, st.2.2.1, st.2.2.2)
      (innerB N nx h))))
  else pure (ForInStep.yield (st.1, st.2.1, st.2.2.1, st.2.2.2))

@[expose] def initSt (N r : Nat) : St := (#[r], #[0], #[0], (Array.replicate N false).set! r true)

theorem idxBFS_eq (N k : Nat) (nx : Nat → Nat → Nat) (r : Nat) :
    idxBFS N k nx r =
      let s := Id.run (forIn (List.range' 0 N) (initSt N r) (outerB N k nx))
      (s.1, s.2.1, s.2.2.1) := by
  unfold idxBFS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

@[expose] def Inv (N cnt : Nat) (T par lab : Nat → Nat) (h j : Nat) (st : St) : Prop :=
  st.1.size ≤ cnt ∧ st.2.1.size = st.1.size ∧ st.2.2.1.size = st.1.size ∧
    (∀ i < st.1.size, st.1[i]! = T i ∧ st.2.1[i]! = par i ∧ st.2.2.1[i]! = lab i) ∧
    st.2.2.2.size = N ∧ (∀ z < N, st.2.2.2[z]! = true ↔ ∃ i < st.1.size, T i = z) ∧
    (∀ i < cnt, i < st.1.size ↔ (i = 0 ∨ Lex (par i) (lab i) h j))

section Search

variable {N k cnt : Nat} {nx : Nat → Nat → Nat} {T par lab : Nat → Nat} {pos : Nat → Nat → Nat}

theorem inner_step (F : Facts N k cnt nx T par lab pos) {h j : Nat} (hh : h < cnt) (hj : j < k)
    {st : St} (hI : Inv N cnt T par lab h j st) :
    ∃ st', innerB N nx h j st = pure (ForInStep.yield st') ∧ Inv N cnt T par lab h (j + 1) st' := by
  obtain ⟨hle, hp, hl, hget, hsz, hseen, hch⟩ := hI
  have hhs : h < st.1.size := by
    rw [hch h hh]
    by_cases h0 : h = 0
    · exact Or.inl h0
    · exact Or.inr (Or.inl (F.tree h (by omega) hh).1)
  have hy : nx st.1[h]! j = nx (T h) j := by rw [(hget h hhs).1]
  have hmove : ∀ i, (i = 0 ∨ Lex (par i) (lab i) h (j + 1)) ↔
      ((i = 0 ∨ Lex (par i) (lab i) h j) ∨ (0 < i ∧ par i = h ∧ lab i = j)) := by
    intro i
    unfold Lex
    omega
  have himg : ∀ i < cnt, 0 < i → par i = h → lab i = j → T i = nx (T h) j := by
    intro i hi h0 hp hl
    rw [← (F.tree i h0 hi).2.2, hp, hl]
  obtain ⟨hq, hx, hor⟩ := F.close h hh j hj
  generalize pos h j = q at hq hx hor
  have hlt : nx (T h) j < N := by rw [hx]; exact F.lt_N q hq
  unfold innerB
  rw [hy]
  by_cases hnew : 0 < q ∧ par q = h ∧ lab q = j
  · obtain ⟨hq0, hpq, hlq⟩ := hnew
    have hqs : ¬ q < st.1.size := by
      rw [hch q hq]
      rintro (e | e)
      · omega
      · rw [hpq, hlq] at e
        exact lex_irrefl e
    have hqm : q = st.1.size := by
      refine Nat.le_antisymm (Nat.le_of_not_lt fun hlt' => ?_) (by omega)
      have hm0 : 0 < st.1.size := by
        have := (hch 0 F.pos_cnt).2 (Or.inl rfl)
        omega
      have hns : ¬ (st.1.size = 0 ∨ Lex (par st.1.size) (lab st.1.size) h j) := by
        rw [← hch st.1.size (by omega)]
        exact Nat.lt_irrefl _
      have := F.order_lt hm0 hlt' hq
      rw [hpq, hlq] at this
      exact hns (Or.inr this)
    have hnc : st.2.2.2[nx (T h) j]! = false := by
      rw [Bool.eq_false_iff]
      intro hc
      obtain ⟨i, hi, e⟩ := (hseen _ hlt).1 hc
      rw [hx] at e
      have := F.inj i (by omega) q hq e
      omega
    refine ⟨(st.1.push (nx (T h) j), st.2.1.push h, st.2.2.1.push j,
      st.2.2.2.set! (nx (T h) j) true), by simp [hlt, hnc], ?_⟩
    unfold Inv
    dsimp only
    refine ⟨?_, by simp [hp], by simp [hl], fun i hi => ?_, by simp [hsz], fun z hz => ?_,
      fun i hi => ?_⟩
    · rw [Array.size_push]
      omega
    · rw [Array.size_push] at hi
      rcases Nat.lt_or_ge i st.1.size with a | a
      · rw [push_lt a, push_lt (by omega : i < st.2.1.size), push_lt (by omega : i < st.2.2.1.size)]
        exact hget i a
      · have e : i = st.1.size := by omega
        subst e
        have e1 : (st.2.1.push h)[st.1.size]! = h := by rw [← hp]; exact push_eq
        have e2 : (st.2.2.1.push j)[st.1.size]! = j := by rw [← hl]; exact push_eq
        refine ⟨?_, ?_, ?_⟩
        · rw [push_eq, ← hqm, hx]
        · rw [e1, ← hqm, hpq]
        · rw [e2, ← hqm, hlq]
    · rw [Array.size_push, set_get (by omega)]
      by_cases e : nx (T h) j = z
      · rw [if_pos e]
        exact iff_of_true rfl ⟨st.1.size, by omega, by rw [← hqm, ← hx, e]⟩
      · rw [if_neg e, hseen z hz]
        constructor
        · rintro ⟨i, hi, e'⟩
          exact ⟨i, by omega, e'⟩
        · rintro ⟨i, hi, e'⟩
          rcases Nat.lt_or_ge i st.1.size with a | a
          · exact ⟨i, a, e'⟩
          · have : i = st.1.size := by omega
            subst this
            rw [← hqm, ← hx] at e'
            exact absurd e' e
    · rw [Array.size_push, hmove i, ← hch i hi]
      constructor
      · intro hlt'
        rcases Nat.lt_or_ge i st.1.size with a | a
        · exact Or.inl a
        · have e : i = st.1.size := by omega
          subst e
          exact Or.inr ⟨by omega, by rw [← hqm]; exact hpq, by rw [← hqm]; exact hlq⟩
      · rintro (a | ⟨a0, a1, a2⟩)
        · omega
        · refine Classical.byContradiction fun hne => ?_
          have hgt : q < i := by omega
          have := F.order_lt hq0 hgt hi
          rw [hpq, hlq, a1, a2] at this
          exact lex_irrefl this
  · have hqs : q < st.1.size := by
      rw [hch q hq]
      rcases hor with e | e
      · exact Or.inl e
      · by_cases h0 : q = 0
        · exact Or.inl h0
        · right
          unfold Lex at e ⊢
          have : ¬ (par q = h ∧ lab q = j) := fun e' => hnew ⟨by omega, e'.1, e'.2⟩
          omega
    have hc : st.2.2.2[nx (T h) j]! = true := (hseen _ hlt).2 ⟨q, hqs, hx.symm⟩
    refine ⟨st, by simp [hc], hle, hp, hl, hget, hsz, hseen, fun i hi => ?_⟩
    rw [hmove i, ← hch i hi]
    constructor
    · exact Or.inl
    · rintro (a | ⟨a0, a1, a2⟩)
      · exact a
      · exfalso
        have := F.inj i hi q hq ((himg i hi a0 a1 a2).trans hx)
        subst this
        exact hnew ⟨a0, a1, a2⟩

theorem inner_spec (F : Facts N k cnt nx T par lab pos) {h : Nat} (hh : h < cnt) {st : St}
    (hI : Inv N cnt T par lab h 0 st) :
    Inv N cnt T par lab (h + 1) 0
      (Id.run (forIn (List.range' 0 k) (st.1, st.2.1, st.2.2.1, st.2.2.2) (innerB N nx h))) := by
  have := forIn_range'_yield k 0 (st.1, st.2.1, st.2.2.1, st.2.2.2) (innerB N nx h)
    (Inv N cnt T par lab h) (fun j hj st' hP => by
      rw [Nat.zero_add]
      exact inner_step F hh hj hP) hI
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := this
  refine ⟨a1, a2, a3, a4, a5, a6, fun i hi => ?_⟩
  rw [a7 i hi]
  have hlab : 0 < i → lab i < k := fun h0 => (F.tree i h0 hi).2.1
  unfold Lex
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

theorem outer_spec (F : Facts N k cnt nx T par lab pos) :
    Inv N cnt T par lab N 0
      (Id.run (forIn (List.range' 0 N) (initSt N (T 0)) (outerB N k nx))) := by
  refine forIn_range'_yield N 0 _ (outerB N k nx) (fun h st => Inv N cnt T par lab h 0 st)
    (fun h _ st hI => ?_) ?_
  · rw [Nat.zero_add]
    rcases Nat.lt_or_ge h cnt with a | a
    · have hhs : h < st.1.size := by
        rw [hI.2.2.2.2.2.2 h a]
        by_cases h0 : h = 0
        · exact Or.inl h0
        · exact Or.inr (Or.inl (F.tree h (by omega) a).1)
      exact ⟨_, by unfold outerB; rw [if_pos hhs], inner_spec F a hI⟩
    · have hns : ¬ h < st.1.size := by have := hI.1; omega
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hI
      refine ⟨st, by unfold outerB; rw [if_neg hns], a1, a2, a3, a4, a5, a6, fun i hi => ?_⟩
      rw [a7 i hi]
      have hpar : 0 < i → par i < i := fun h0 => (F.tree i h0 hi).1
      unfold Lex
      constructor
      · rintro (e | e)
        · exact Or.inl e
        · by_cases h0 : i = 0
          · exact Or.inl h0
          · have := hpar (by omega)
            exact Or.inr (Or.inl (by omega))
      · rintro (e | e)
        · exact Or.inl e
        · by_cases h0 : i = 0
          · exact Or.inl h0
          · have := hpar (by omega)
            exact Or.inr (Or.inl (by omega))
  · have hr : T 0 < N := F.lt_N 0 F.pos_cnt
    unfold Inv initSt
    dsimp only
    refine ⟨by simp; exact F.pos_cnt, rfl, rfl, fun i hi => ?_, by simp, fun z hz => ?_,
      fun i hi => ?_⟩
    · have : i = 0 := by simp at hi; omega
      subst this
      simp [F.par_zero, F.lab_zero]
    · rw [set_get (by simp; omega)]
      by_cases e : T 0 = z
      · rw [if_pos e]
        exact iff_of_true rfl ⟨0, by simp, e⟩
      · rw [if_neg e, getElem!_pos (Array.replicate N false) z (by simp; omega),
          Array.getElem_replicate]
        refine iff_of_false (by simp) fun ⟨i, hi, e'⟩ => e ?_
        have : i = 0 := by simp at hi; omega
        subst this
        exact e'
    · simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
      unfold Lex
      omega

end Search

theorem idxBFS_replay {N k cnt : Nat} {nx : Nat → Nat → Nat} {T par lab : Nat → Nat}
    {pos : Nat → Nat → Nat} (F : Facts N k cnt nx T par lab pos) :
    idxBFS N k nx (T 0) = (Array.ofFn (n := cnt) fun i => T i.val,
      Array.ofFn (n := cnt) fun i => par i.val, Array.ofFn (n := cnt) fun i => lab i.val) := by
  have hO := outer_spec F
  rw [idxBFS_eq]
  generalize Id.run (forIn (List.range' 0 N) (initSt N (T 0)) (outerB N k nx)) = s at hO
  obtain ⟨hle, hp, hl, hget, -, -, hch⟩ := hO
  have hsz : s.1.size = cnt := by
    refine Nat.le_antisymm hle ?_
    have := F.pos_cnt
    have := F.cnt_le
    have h1 := (hch (cnt - 1) (by omega)).2 (by
      by_cases h0 : cnt - 1 = 0
      · exact Or.inl h0
      · have := (F.tree (cnt - 1) (by omega) (by omega)).1
        exact Or.inr (Or.inl (by omega)))
    omega
  have ext : ∀ (a : Array Nat) (f : Nat → Nat), a.size = cnt → (∀ i < cnt, a[i]! = f i) →
      a = Array.ofFn (n := cnt) fun i => f i.val := fun a f ha hf => by
    apply Array.ext
    · simp [ha]
    · intro i h1 h2
      rw [Array.getElem_ofFn, ← getElem!_pos a i h1, hf i (by omega)]
  dsimp only
  rw [ext s.1 T hsz fun i hi => (hget i (by omega)).1,
    ext s.2.1 par (by omega) fun i hi => (hget i (by omega)).2.1,
    ext s.2.2.1 lab (by omega) fun i hi => (hget i (by omega)).2.2]

end CFSG.KS.IdxBfs

end
