module

public import CFSG.Certificates.Kernel.Spor.HBfsReplay

public section

namespace CFSG.KS.HBfs

open CFSG.KS.BfsReplay

structure HReplayT {α : Type} (key : α → UInt64) (step : Nat → α → α) (k : Nat) (root : α)
    (cnt cap : Nat) (T : Nat → α) (par lab : Nat → Nat) (pos : Nat → Nat → Nat) : Prop where
  pos_cnt : 0 < cnt
  root_eq : T 0 = root
  par_zero : par 0 = 0
  lab_zero : lab 0 = 0
  kinj : ∀ a < cnt, ∀ b < cnt, key (T a) = key (T b) → a = b
  tree : ∀ i, 0 < i → i < cnt → par i < i ∧ lab i < k ∧ T i = step (lab i) (T (par i))
  par_cap : ∀ i, 0 < i → i < cnt → par i < cap
  order : ∀ i, 0 < i → i + 1 < cnt → LexLt (par i) (lab i) (par (i + 1)) (lab (i + 1))
  close : ∀ h < cnt, h < cap → ∀ j < k, pos h j < cnt ∧ step j (T h) = T (pos h j) ∧
    (pos h j = 0 ∨ ¬ LexLt h j (par (pos h j)) (lab (pos h j)))

section

variable {α : Type} [Inhabited α]
variable {key : α → UInt64} {step : Nat → α → α} {k : Nat} {root : α} {cnt cap : Nat}
  {T : Nat → α} {par lab : Nat → Nat} {pos : Nat → Nat → Nat}

omit [Inhabited α] in
theorem HReplayT.order_lt (R : HReplayT key step k root cnt cap T par lab pos) {i i' : Nat}
    (h0 : 0 < i) (hi : i < i') (hi' : i' < cnt) : LexLt (par i) (lab i) (par i') (lab i') := by
  induction i' with
  | zero => omega
  | succ i' ih =>
    rcases Nat.lt_or_ge i i' with a | a
    · exact lex_trans (ih a (by omega)) (R.order i' (by omega) hi')
    · have e : i = i' := by omega
      subst e
      exact R.order i h0 hi'

theorem hinvT_init (R : HReplayT key step k root cnt cap T par lab pos) :
    HInv key cnt T par lab 0 0 (hInit key root) := by
  refine ⟨by simp [hInit]; exact R.pos_cnt, rfl, rfl, fun i hi => ?_, fun u => ?_, fun i hi => ?_⟩
  · have : i = 0 := by simp [hInit] at hi; omega
    subst this
    simp [hInit, R.root_eq, R.par_zero, R.lab_zero]
  · simp only [hInit]
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
    constructor
    · intro e
      exact ⟨0, by simp, by rw [R.root_eq]; exact beq_iff_eq.1 e⟩
    · rintro ⟨i, hi, e⟩
      have : i = 0 := by simp at hi; omega
      subst this
      rw [← e, R.root_eq]
      exact beq_self_eq_true _
  · simp only [hInit, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
    unfold LexLt
    constructor
    · intro h
      exact Or.inl (by omega)
    · rintro (e | e)
      · omega
      · omega

theorem hinnerT_step (R : HReplayT key step k root cnt cap T par lab pos) {h j : Nat}
    (hh : h < cnt) (hc : h < cap) (hj : j < k) {s : HSt α} (hI : HInv key cnt T par lab h j s) :
    ∃ s', hInner key step (T h) h j s = pure (ForInStep.yield s') ∧
      HInv key cnt T par lab h (j + 1) s' ∧ s.2.1.size ≤ s'.2.1.size := by
  obtain ⟨hle, hp, hl, hget, hK, hch⟩ := hI
  obtain ⟨hq, hx, hor⟩ := R.close h hh hc j hj
  generalize hqdef : pos h j = q at hq hx hor
  have hmove : ∀ i < cnt, (i = 0 ∨ LexLt (par i) (lab i) h (j + 1)) ↔
      ((i = 0 ∨ LexLt (par i) (lab i) h j) ∨ (0 < i ∧ par i = h ∧ lab i = j)) := by
    intro i _
    unfold LexLt
    omega
  by_cases hnew : 0 < q ∧ par q = h ∧ lab q = j
  · obtain ⟨hq0, hpq, hlq⟩ := hnew
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
      have := R.order_lt hm0 hlt hq
      rw [hpq, hlq] at this
      unfold LexLt at this hns
      omega
    have hnc : s.1.contains (key (step j (T h))) = false := by
      rw [Bool.eq_false_iff]
      intro hc'
      obtain ⟨i, hi, e⟩ := (hK _).1 hc'
      rw [hx] at e
      have := R.kinj i (by omega) q hq e
      omega
    refine ⟨(s.1.insert (key (step j (T h))), s.2.1.push (step j (T h)), s.2.2.1.push h,
      s.2.2.2.push j), by simp [hInner, hnc], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp⟩
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
        · change (s.2.1.push (step j (T h)))[s.2.1.size]! = T s.2.1.size
          rw [push_eq, ← hqm, hx]
        · change (s.2.2.1.push h)[s.2.1.size]! = par s.2.1.size
          rw [e1, ← hqm, hpq]
        · change (s.2.2.2.push j)[s.2.1.size]! = lab s.2.1.size
          rw [e2, ← hqm, hlq]
    · intro u
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
          have := R.order_lt hq0 hgt hi
          rw [hpq, hlq, a1, a2] at this
          exact lex_irrefl this
  · have hqs : q < s.2.1.size := by
      rw [hch q hq]
      rcases hor with e | e
      · exact Or.inl e
      · by_cases h0 : q = 0
        · exact Or.inl h0
        · right
          unfold LexLt at e ⊢
          have : ¬ (par q = h ∧ lab q = j) := fun e' => hnew ⟨by omega, e'.1, e'.2⟩
          omega
    have hc' : s.1.contains (key (step j (T h))) = true := (hK _).2 ⟨q, hqs, by rw [hx]⟩
    refine ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), by simp [hInner, hc'],
      ⟨hle, hp, hl, hget, hK, fun i hi => ?_⟩, Nat.le_refl _⟩
    rw [hmove i hi, ← hch i hi]
    constructor
    · exact Or.inl
    · rintro (a | ⟨a0, a1, a2⟩)
      · exact a
      · exfalso
        have e : key (T i) = key (T q) := by
          rw [← hx, (R.tree i a0 hi).2.2, a1, a2]
        have := R.kinj i hi q hq e
        subst this
        exact hnew ⟨a0, a1, a2⟩

theorem hinnerT_spec (R : HReplayT key step k root cnt cap T par lab pos) {h : Nat}
    (hh : h < cnt) (hc : h < cap) {s : HSt α} (hI : HInv key cnt T par lab h 0 s)
    (hhs : h < s.2.1.size) :
    HInv key cnt T par lab (h + 1) 0
      (Id.run (forIn (List.range' 0 k) (s.1, s.2.1, s.2.2.1, s.2.2.2)
        (hInner key step s.2.1[h]! h))) := by
  have hT : s.2.1[h]! = T h := (hI.2.2.2.1 h hhs).1
  rw [hT]
  have := forIn_range'_yield k 0 (s.1, s.2.1, s.2.2.1, s.2.2.2) (hInner key step (T h) h)
    (fun j s' => HInv key cnt T par lab h j s' ∧ s.2.1.size ≤ s'.2.1.size)
    (fun j hj s' hP => by
      rw [Nat.zero_add]
      obtain ⟨s'', e, hI', hle⟩ := hinnerT_step R hh hc hj hP.1
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

theorem houterT_spec (R : HReplayT key step k root cnt cap T par lab pos) :
    ∃ h, HInv key cnt T par lab h 0
        (Id.run (forIn (List.range' 0 cap) (hInit key root) (hOuter key step k))) ∧
      ∀ i, 0 < i → i < cnt → par i < h := by
  refine forIn_range'_done cap 0 (hInit key root) (hOuter key step k)
    (fun h s => h ≤ cnt ∧ HInv key cnt T par lab h 0 s)
    (fun s => ∃ h, HInv key cnt T par lab h 0 s ∧ ∀ i, 0 < i → i < cnt → par i < h)
    (fun h hh s hP => ?_) (fun s hP => ⟨cap, hP.2, R.par_cap⟩) ⟨Nat.zero_le _, hinvT_init R⟩
  obtain ⟨hhc, hI⟩ := hP
  rw [Nat.zero_add]
  rcases Nat.lt_or_ge h cnt with a | a
  · have hhs : h < s.2.1.size := by
      rw [hI.2.2.2.2.2 h a]
      by_cases h0 : h = 0
      · exact Or.inl h0
      · right
        left
        exact (R.tree h (by omega) a).1
    exact Or.inl ⟨_, by simp [hOuter, hhs], by omega, hinnerT_spec R a hh hI hhs⟩
  · have e : h = cnt := by omega
    subst e
    have hns : ¬ h < s.2.1.size := by have := hI.1; omega
    exact Or.inr ⟨_, by simp [hOuter, hns], h, hI, fun i _ hi => by
      have := (R.tree i (by omega) hi).1
      omega⟩

theorem hbfs_replayT (R : HReplayT key step k root cnt cap T par lab pos) :
    hbfs key step k root cap = (Array.ofFn (n := cnt) fun i => T i.val,
      Array.ofFn (n := cnt) fun i => par i.val, Array.ofFn (n := cnt) fun i => lab i.val) := by
  obtain ⟨h, hO, hpar⟩ := houterT_spec R
  rw [hbfs_eq]
  generalize Id.run (forIn (List.range' 0 cap) (hInit key root) (hOuter key step k)) = s at hO
  obtain ⟨hle, hp, hl, hget, -, hch⟩ := hO
  have hsz : s.2.1.size = cnt := by
    have := (hch (cnt - 1) (by have := R.pos_cnt; omega)).2 (by
      by_cases h0 : cnt - 1 = 0
      · exact Or.inl h0
      · right
        left
        exact hpar (cnt - 1) (by omega) (by have := R.pos_cnt; omega))
    omega
  have ext : ∀ {β : Type} [Inhabited β] (a : Array β) (f : Nat → β), a.size = cnt →
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

end

end CFSG.KS.HBfs

end
