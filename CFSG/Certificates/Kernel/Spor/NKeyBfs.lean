module

public import CFSG.Certificates.Kernel.Spor.BfsReplay
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.Loops
public import Std.Data.HashSet.Lemmas

public section

namespace CFSG.KS.NKey

open CFSG.KS.BfsReplay CFSG.KC.Enum

section

variable {α : Type} [Inhabited α]

@[expose] def nkbfs (sk : Nat → α → Nat) (st : Nat → α → α) (k : Nat) (root : α) (key0 cap : Nat) :
    Array α × Array Nat × Array Nat := Id.run do
  let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert key0
  let mut elts : Array α := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for h in [0:cap] do
    if h < elts.size then
      let y := elts[h]!
      for l in [0:k] do
        let kz := sk l y
        if !seen.contains kz then
          seen := seen.insert kz
          elts := elts.push (st l y)
          par := par.push h
          lab := lab.push l
    else break
  return (elts, par, lab)

structure NKRec (sk : Nat → α → Nat) (st : Nat → α → α) (κ : α → Nat) (k : Nat) (root : α)
    (key0 cnt : Nat) (T : Nat → α) (par lab : Nat → Nat) (pos : Nat → Nat → Nat) : Prop where
  pos_cnt : 0 < cnt
  root_eq : T 0 = root
  key0_eq : key0 = κ root
  par_zero : par 0 = 0
  lab_zero : lab 0 = 0
  kinj : ∀ a < cnt, ∀ b < cnt, κ (T a) = κ (T b) → a = b
  tree : ∀ i, 0 < i → i < cnt → par i < i ∧ lab i < k ∧ sk (lab i) (T (par i)) = κ (T i) ∧
    st (lab i) (T (par i)) = T i
  order : ∀ i, 0 < i → i + 1 < cnt → LexLt (par i) (lab i) (par (i + 1)) (lab (i + 1))
  close : ∀ h < cnt, ∀ j < k, pos h j < cnt ∧ sk j (T h) = κ (T (pos h j)) ∧
    (pos h j = 0 ∨ ¬ LexLt h j (par (pos h j)) (lab (pos h j)))

abbrev NSt (α : Type) := Std.HashSet Nat × Array α × Array Nat × Array Nat

@[expose] def nInner (sk : Nat → α → Nat) (st : Nat → α → α) (y : α) (h l : Nat) (s : NSt α) :
    Id (ForInStep (NSt α)) :=
  if (!s.1.contains (sk l y)) = true then
    pure (ForInStep.yield (s.1.insert (sk l y), s.2.1.push (st l y), s.2.2.1.push h,
      s.2.2.2.push l))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def nOuter (sk : Nat → α → Nat) (st : Nat → α → α) (k h : Nat) (s : NSt α) :
    Id (ForInStep (NSt α)) :=
  if h < s.2.1.size then
    pure (ForInStep.yield (Id.run (forIn (List.range' 0 k) (s.1, s.2.1, s.2.2.1, s.2.2.2)
      (nInner sk st s.2.1[h]! h))))
  else pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def nInit (root : α) (key0 : Nat) : NSt α :=
  ((∅ : Std.HashSet Nat).insert key0, #[root], #[0], #[0])

theorem nkbfs_eq (sk : Nat → α → Nat) (st : Nat → α → α) (k : Nat) (root : α) (key0 cap : Nat) :
    nkbfs sk st k root key0 cap =
      let s := Id.run (forIn (List.range' 0 cap) (nInit root key0) (nOuter sk st k))
      (s.2.1, s.2.2.1, s.2.2.2) := by
  unfold nkbfs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

@[expose] def NInv (κ : α → Nat) (cnt : Nat) (T : Nat → α) (par lab : Nat → Nat) (h j : Nat)
    (s : NSt α) : Prop :=
  s.2.1.size ≤ cnt ∧ s.2.2.1.size = s.2.1.size ∧ s.2.2.2.size = s.2.1.size ∧
    (∀ i < s.2.1.size, s.2.1[i]! = T i ∧ s.2.2.1[i]! = par i ∧ s.2.2.2[i]! = lab i) ∧
    (∀ u, s.1.contains u = true ↔ ∃ i < s.2.1.size, κ (T i) = u) ∧
    (∀ i < cnt, i < s.2.1.size ↔ (i = 0 ∨ LexLt (par i) (lab i) h j))

variable {sk : Nat → α → Nat} {st : Nat → α → α} {κ : α → Nat} {k : Nat} {root : α}
  {key0 cnt : Nat} {T : Nat → α} {par lab : Nat → Nat} {pos : Nat → Nat → Nat}

omit [Inhabited α] in
theorem NKRec.order_lt (R : NKRec sk st κ k root key0 cnt T par lab pos) {i i' : Nat}
    (h0 : 0 < i) (hi : i < i') (hi' : i' < cnt) : LexLt (par i) (lab i) (par i') (lab i') := by
  induction i' with
  | zero => omega
  | succ i' ih =>
    rcases Nat.lt_or_ge i i' with a | a
    · exact lex_trans (ih a (by omega)) (R.order i' (by omega) hi')
    · have e : i = i' := by omega
      subst e
      exact R.order i h0 hi'

theorem ninv_init (R : NKRec sk st κ k root key0 cnt T par lab pos) :
    NInv κ cnt T par lab 0 0 (nInit root key0) := by
  refine ⟨by simp [nInit]; exact R.pos_cnt, rfl, rfl, fun i hi => ?_, fun u => ?_, fun i hi => ?_⟩
  · have : i = 0 := by simp [nInit] at hi; omega
    subst this
    simp [nInit, R.root_eq, R.par_zero, R.lab_zero]
  · simp only [nInit]
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
    constructor
    · intro e
      exact ⟨0, by simp, by rw [R.root_eq, ← R.key0_eq]; exact beq_iff_eq.1 e⟩
    · rintro ⟨i, hi, e⟩
      have : i = 0 := by simp at hi; omega
      subst this
      rw [← e, R.root_eq, ← R.key0_eq]
      exact beq_self_eq_true _
  · simp only [nInit, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
    unfold LexLt
    constructor
    · intro h
      exact Or.inl (by omega)
    · rintro (e | e)
      · omega
      · omega

theorem ninner_step (R : NKRec sk st κ k root key0 cnt T par lab pos) {h j : Nat} (hh : h < cnt)
    (hj : j < k) {s : NSt α} (hI : NInv κ cnt T par lab h j s) :
    ∃ s', nInner sk st (T h) h j s = pure (ForInStep.yield s') ∧
      NInv κ cnt T par lab h (j + 1) s' ∧ s.2.1.size ≤ s'.2.1.size := by
  obtain ⟨hle, hp, hl, hget, hK, hch⟩ := hI
  obtain ⟨hq, hx, hor⟩ := R.close h hh j hj
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
    have hst : st j (T h) = T q := by
      have := (R.tree q hq0 hq).2.2.2
      rwa [hpq, hlq] at this
    have hnc : s.1.contains (sk j (T h)) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      obtain ⟨i, hi, e⟩ := (hK _).1 hc
      rw [hx] at e
      have := R.kinj i (by omega) q hq e
      omega
    refine ⟨(s.1.insert (sk j (T h)), s.2.1.push (st j (T h)), s.2.2.1.push h,
      s.2.2.2.push j), by simp [nInner, hnc], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp⟩
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
          rw [push_eq, ← hqm, hst]
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
    have hc : s.1.contains (sk j (T h)) = true := (hK _).2 ⟨q, hqs, by rw [hx]⟩
    refine ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), by simp [nInner, hc],
      ⟨hle, hp, hl, hget, hK, fun i hi => ?_⟩, Nat.le_refl _⟩
    rw [hmove i hi, ← hch i hi]
    constructor
    · exact Or.inl
    · rintro (a | ⟨a0, a1, a2⟩)
      · exact a
      · exfalso
        have e : κ (T i) = κ (T q) := by
          rw [← hx, ← (R.tree i a0 hi).2.2.1, a1, a2]
        have := R.kinj i hi q hq e
        subst this
        exact hnew ⟨a0, a1, a2⟩

theorem ninner_spec (R : NKRec sk st κ k root key0 cnt T par lab pos) {h : Nat} (hh : h < cnt)
    {s : NSt α} (hI : NInv κ cnt T par lab h 0 s) (hhs : h < s.2.1.size) :
    NInv κ cnt T par lab (h + 1) 0
      (Id.run (forIn (List.range' 0 k) (s.1, s.2.1, s.2.2.1, s.2.2.2)
        (nInner sk st s.2.1[h]! h))) := by
  have hT : s.2.1[h]! = T h := (hI.2.2.2.1 h hhs).1
  rw [hT]
  have := forIn_range'_yield k 0 (s.1, s.2.1, s.2.2.1, s.2.2.2) (nInner sk st (T h) h)
    (fun j s' => NInv κ cnt T par lab h j s' ∧ s.2.1.size ≤ s'.2.1.size)
    (fun j hj s' hP => by
      rw [Nat.zero_add]
      obtain ⟨s'', e, hI', hle⟩ := ninner_step R hh hj hP.1
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

theorem nouter_spec (R : NKRec sk st κ k root key0 cnt T par lab pos) {cap : Nat}
    (hcap : cnt ≤ cap) :
    NInv κ cnt T par lab cnt 0
      (Id.run (forIn (List.range' 0 cap) (nInit root key0) (nOuter sk st k))) := by
  refine forIn_range'_done cap 0 (nInit root key0) (nOuter sk st k)
    (fun h s => h ≤ cnt ∧ NInv κ cnt T par lab h 0 s) (NInv κ cnt T par lab cnt 0)
    (fun h hh s hP => ?_) (fun s hP => ?_) ⟨Nat.zero_le _, ninv_init R⟩
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
      exact Or.inl ⟨_, by simp [nOuter, hhs], by omega, ninner_spec R a hI hhs⟩
    · have e : h = cnt := by omega
      subst e
      have hns : ¬ h < s.2.1.size := by have := hI.1; omega
      exact Or.inr ⟨_, by simp [nOuter, hns], hI⟩
  · have e : cap = cnt ∨ cnt < cap := by omega
    rcases e with e | e
    · have h2 := hP.2
      rw [e] at h2
      exact h2
    · exact absurd hP.1 (by omega)

theorem nkbfs_rec (R : NKRec sk st κ k root key0 cnt T par lab pos) {cap : Nat}
    (hcap : cnt ≤ cap) :
    nkbfs sk st k root key0 cap = (Array.ofFn (n := cnt) fun i => T i.val,
      Array.ofFn (n := cnt) fun i => par i.val, Array.ofFn (n := cnt) fun i => lab i.val) := by
  have hO := nouter_spec R hcap
  rw [nkbfs_eq]
  generalize Id.run (forIn (List.range' 0 cap) (nInit root key0) (nOuter sk st k)) = s at hO
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

@[expose] noncomputable def runC (f : Nat → Nat → Nat → Nat) (k : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ cur => cur)
    (fun _ ih h cur => strictN (foldUp k (fun l cur => f h l cur) cur)
      (fun c' => strictN (Nat.succ h) (fun h' => ih h' c')))

@[expose] def curE (f : Nat → Nat → Nat → Nat) (k c0 e : Nat) : Nat :=
  (List.range e).foldl (fun s e' => f (e' / k) (e' % k) s) c0

theorem curE_zero (f : Nat → Nat → Nat → Nat) (k c0 : Nat) : curE f k c0 0 = c0 := rfl

theorem curE_succ (f : Nat → Nat → Nat → Nat) (k c0 e : Nat) :
    curE f k c0 (e + 1) = f (e / k) (e % k) (curE f k c0 e) := by
  unfold curE
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem runC_succ (f : Nat → Nat → Nat → Nat) (k len h cur : Nat) :
    runC f k (len + 1) h cur = runC f k len (h + 1) (foldUp k (fun l cur => f h l cur) cur) := by
  change strictN (foldUp k (fun l cur => f h l cur) cur)
    (fun c' => strictN (Nat.succ h) (fun h' => runC f k len h' c')) = _
  rw [CFSG.KS.Raw.Orb.strictN_eq, CFSG.KS.Raw.Orb.strictN_eq]

theorem foldUp_curE {f : Nat → Nat → Nat → Nat} {k : Nat} (c0 h : Nat) :
    foldUp k (fun l cur => f h l cur) (curE f k c0 (k * h)) = curE f k c0 (k * h + k) := by
  rw [CFSG.KS.Raw.Orb.foldUp_eq]
  have key : ∀ l ≤ k, (List.range l).foldl (fun s i => f h i s) (curE f k c0 (k * h)) =
      curE f k c0 (k * h + l) := by
    intro l
    induction l with
    | zero => intro _; rfl
    | succ l ih =>
      intro hl
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega),
        ← Nat.add_assoc, curE_succ]
      have hk : 0 < k := by omega
      have e1 : (k * h + l) / k = h := by
        rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt (by omega),
          Nat.zero_add]
      have e2 : (k * h + l) % k = l := by
        rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [e1, e2]
  exact key k (Nat.le_refl k)

theorem runC_curE (f : Nat → Nat → Nat → Nat) (k c0 : Nat) :
    ∀ len h, runC f k len h (curE f k c0 (k * h)) = curE f k c0 (k * (h + len)) := by
  intro len
  induction len with
  | zero => intro h; rfl
  | succ len ih =>
    intro h
    have e : k * h + k = k * (h + 1) := (Nat.mul_succ k h).symm
    rw [runC_succ, foldUp_curE, e, ih (h + 1)]
    congr 2
    omega

section

variable {α : Type} {sk : Nat → α → Nat} {st : Nat → α → α} {κ : α → Nat} {k : Nat} {root : α}
  {key0 c : Nat} {T : Nat → α} {P L : Nat → Nat} {pos : Nat → Nat → Nat}
  {f : Nat → Nat → Nat → Nat}

@[expose] def StepOK (sk : Nat → α → Nat) (st : Nat → α → α) (κ : α → Nat) (c : Nat)
    (T : Nat → α) (P L : Nat → Nat) (pos : Nat → Nat → Nat) (f : Nat → Nat → Nat → Nat)
    (h l cur : Nat) : Prop :=
  (h < cur ∧ pos h l < cur ∧ f h l cur = cur ∧ (cur ≤ c → sk l (T h) = κ (T (pos h l)))) ∨
    (h < cur ∧ pos h l = cur ∧ f h l cur = cur + 1 ∧
      (cur < c → sk l (T h) = κ (T cur) ∧ st l (T h) = T cur ∧ P cur = h ∧ L cur = l)) ∨
    (cur ≤ h ∧ cur = c ∧ f h l cur = cur)

theorem lex_of_lt {k a b c d : Nat} (hd : d < k) (h : k * a + b < k * c + d) :
    LexLt a b c d := by
  unfold LexLt
  rcases Nat.lt_trichotomy a c with h1 | h1 | h1
  · exact Or.inl h1
  · subst h1
    exact Or.inr ⟨rfl, by omega⟩
  · exfalso
    have : k * (c + 1) ≤ k * a := Nat.mul_le_mul_left k h1
    rw [Nat.mul_succ] at this
    omega

theorem lt_of_lex {k a b c d : Nat} (hb : b < k) (h : LexLt a b c d) : k * a + b < k * c + d := by
  unfold LexLt at h
  rcases h with h | ⟨rfl, h⟩
  · have : k * (a + 1) ≤ k * c := Nat.mul_le_mul_left k h
    rw [Nat.mul_succ] at this
    omega
  · omega

theorem group_idx {R t N : Nat} (ht : t < N * R) :
    t / R < N ∧ t % R < R ∧ Nat.add (Nat.mul (t / R) R) (t % R) = t := by
  have hR : 0 < R := by
    rcases Nat.eq_zero_or_pos R with h0 | h0
    · rw [h0, Nat.mul_zero] at ht
      exact absurd ht (Nat.not_lt_zero _)
    · exact h0
  refine ⟨(Nat.div_lt_iff_lt_mul hR).2 ht, Nat.mod_lt _ hR, ?_⟩
  change t / R * R + t % R = t
  rw [Nat.mul_comm]
  exact Nat.div_add_mod t R

theorem slices_of_groups {F : Nat → Nat → Nat} {C : Nat → Nat} {nS R H : Nat}
    (h : ∀ g < nS, ∀ r < R, Nat.beq (F (Nat.mul (Nat.add (Nat.mul g R) r) H)
      (C (Nat.add (Nat.mul g R) r))) (C (Nat.succ (Nat.add (Nat.mul g R) r))) = true) :
    ∀ t < nS * R, F (t * H) (C t) = C (t + 1) := by
  intro t ht
  obtain ⟨h1, h2, e⟩ := group_idx ht
  have := Nat.eq_of_beq_eq_true (h _ h1 _ h2)
  rw [e] at this
  exact this

theorem all_of_blocks {f : Nat → Bool} {nB R B N : Nat} (hc : N ≤ nB * R * B)
    (h : ∀ g < nB, ∀ r < R, CFSG.KC.Enum.allBlk (Nat.mul (Nat.add (Nat.mul g R) r) B) f B = true) :
    ∀ i < N, f i = true := by
  intro i hi
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · rw [h0, Nat.mul_zero] at hc
      omega
    · exact h0
  have hiB : i / B < nB * R := by
    rw [Nat.div_lt_iff_lt_mul hB]
    exact Nat.lt_of_lt_of_le hi hc
  obtain ⟨h1, h2, e⟩ := group_idx hiB
  have h3 := CFSG.KS.allBlk_spec (h _ h1 _ h2) (i % B) (Nat.mod_lt _ hB)
  rw [e] at h3
  have e2 : Nat.add (Nat.mul (i / B) B) (i % B) = i := by
    change i / B * B + i % B = i
    rw [Nat.mul_comm]
    exact Nat.div_add_mod i B
  rwa [e2] at h3

theorem ivt {s : Nat → Nat} {i : Nat} : ∀ E, (∀ e < E, s e ≤ s (e + 1) ∧ s (e + 1) ≤ s e + 1) →
    s 0 ≤ i → i < s E → ∃ e < E, s e = i ∧ s (e + 1) = i + 1
  | 0, _, h0, h1 => absurd h1 (by omega)
  | E + 1, hs, h0, h1 => by
    by_cases h : i < s E
    · obtain ⟨e, he, h2⟩ := ivt E (fun e he => hs e (by omega)) h0 h
      exact ⟨e, by omega, h2⟩
    · have := hs E (by omega)
      exact ⟨E, by omega, by omega, by omega⟩

theorem mono_le {s : Nat → Nat} {E : Nat} (hs : ∀ e < E, s e ≤ s (e + 1)) {e e' : Nat}
    (h : e ≤ e') (h' : e' ≤ E) : s e ≤ s e' := by
  have key : ∀ d, e + d ≤ E → s e ≤ s (e + d) := by
    intro d
    induction d with
    | zero => intro _; exact Nat.le_refl _
    | succ d ih =>
      intro hd
      rw [← Nat.add_assoc]
      exact Nat.le_trans (ih (by omega)) (hs _ (by omega))
  have := key (e' - e) (by omega)
  rwa [Nat.add_sub_cancel' h] at this

theorem divmod_eq {k : Nat} (h : Nat) {j : Nat} (hj : j < k) : (k * h + j) / k = h ∧ (k * h + j) % k = j := by
  have hk : 0 < k := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem runC_rec {fl M H : Nat} {C : Nat → Nat} (hc0 : 0 < c) (hcM : c ≤ M * H)
    (hfl : c ≠ fl) (hC0 : C 0 = 1) (hCM : C M = c)
    (hrun : ∀ t < M, runC f k H (t * H) (C t) = C (t + 1))
    (habs : ∀ h l, l < k → f h l fl = fl)
    (hstep : ∀ h l cur, l < k → f h l cur ≠ fl → StepOK sk st κ c T P L pos f h l cur)
    (hroot : T 0 = root) (hkey0 : key0 = κ root) (hP0 : P 0 = 0) (hL0 : L 0 = 0)
    (hinj : ∀ a < c, ∀ b < c, κ (T a) = κ (T b) → a = b) :
    NKRec sk st κ k root key0 c T P L pos := by
  have hs0 : curE f k 1 0 = 1 := rfl
  have hsS : ∀ e, curE f k 1 (e + 1) = f (e / k) (e % k) (curE f k 1 e) := curE_succ f k 1
  have hslice : ∀ t ≤ M, curE f k 1 (k * (t * H)) = C t := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [Nat.zero_mul, Nat.mul_zero, hC0]
      rfl
    | succ t ih =>
      intro ht
      rw [← hrun t (by omega), ← ih (by omega), runC_curE]
      congr 1
      rw [Nat.add_mul, Nat.one_mul]
  have hE : curE f k 1 (k * (M * H)) = c := by rw [hslice M (Nat.le_refl M), hCM]
  clear hslice hrun
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  ·
    subst hk0
    rw [Nat.zero_mul] at hE
    have hc1 : c = 1 := by rw [← hE]; rfl
    subst hc1
    exact ⟨Nat.one_pos, hroot, hkey0, hP0, hL0, hinj, fun i hi0 hic => by omega,
      fun i hi0 hi1 => by omega, fun h hh j hj => by omega⟩
  have hEc : k * c ≤ k * (M * H) := Nat.mul_le_mul_left k hcM
  generalize k * (M * H) = E at hE hEc
  generalize curE f k 1 = s at hs0 hsS hE
  have hmod : ∀ e, e % k < k := fun e => Nat.mod_lt _ hk
  have hnf : ∀ e ≤ E, s e ≠ fl := by
    intro e he hse
    have : ∀ d, e + d ≤ E → s (e + d) = fl := by
      intro d
      induction d with
      | zero => intro _; exact hse
      | succ d ih =>
        intro hd
        rw [← Nat.add_assoc, hsS, ih (by omega), habs _ _ (hmod _)]
    have := this (E - e) (by omega)
    rw [Nat.add_sub_cancel' he, hE] at this
    exact hfl this
  have hok : ∀ e < E, StepOK sk st κ c T P L pos f (e / k) (e % k) (s e) := fun e he =>
    hstep _ _ _ (hmod e) (by rw [← hsS]; exact hnf (e + 1) (by omega))
  have hstep1 : ∀ e < E, s e ≤ s (e + 1) ∧ s (e + 1) ≤ s e + 1 := by
    intro e he
    rw [hsS]
    rcases hok e he with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3⟩ <;> rw [h3] <;> omega
  have hmono : ∀ e e', e ≤ e' → e' ≤ E → s e ≤ s e' := fun e e' h h' =>
    mono_le (fun e he => (hstep1 e he).1) h h'
  have hle : ∀ e ≤ E, s e ≤ c := fun e he => hE ▸ hmono e E he (Nat.le_refl E)
  have hcre : ∀ i, 0 < i → i < c → k * P i + L i < E ∧ s (k * P i + L i) = i ∧
      P i < i ∧ L i < k ∧ sk (L i) (T (P i)) = κ (T i) ∧ st (L i) (T (P i)) = T i := by
    intro i hi0 hic
    obtain ⟨e, he, h1, h2⟩ := ivt (s := s) (i := i) E hstep1 (by rw [hs0]; omega) (by rw [hE]; exact hic)
    rcases hok e he with ⟨-, -, h3, -⟩ | ⟨hh, -, -, h4⟩ | ⟨-, -, h3⟩
    · rw [hsS, h3] at h2
      omega
    · rw [h1] at hh h4
      obtain ⟨a1, a2, a3, a4⟩ := h4 hic
      have he' : e = k * P i + L i := by rw [a3, a4]; exact (Nat.div_add_mod e k).symm
      rw [← he', a3, a4]
      exact ⟨he, h1, hh, hmod e, a1, a2⟩
    · rw [hsS, h3] at h2
      omega
  refine ⟨hc0, hroot, hkey0, hP0, hL0, hinj, fun i hi0 hic => ?_, fun i hi0 hi1 => ?_,
    fun h hh j hj => ?_⟩
  · obtain ⟨-, -, a1, a2, a3, a4⟩ := hcre i hi0 hic
    exact ⟨a1, a2, a3, a4⟩
  · obtain ⟨b0, b1, -, b2, -, -⟩ := hcre i hi0 (by omega)
    obtain ⟨c0, c1, -, c2, -, -⟩ := hcre (i + 1) (by omega) hi1
    refine lex_of_lt c2 (Nat.lt_of_not_le fun hle' => ?_)
    have := hmono _ _ hle' (Nat.le_of_lt b0)
    rw [c1, b1] at this
    omega
  · have hd := divmod_eq h hj
    have he : k * h + j < E := by
      have : k * (h + 1) ≤ k * c := Nat.mul_le_mul_left k hh
      rw [Nat.mul_succ] at this
      omega
    have hsc := hle (k * h + j) (Nat.le_of_lt he)
    have hsc1 := hle (k * h + j + 1) he
    have hs1 := hsS (k * h + j)
    have hO := hok _ he
    rw [hd.1, hd.2] at hO hs1
    rcases hO with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3⟩
    · refine ⟨by omega, a4 hsc, ?_⟩
      rcases Nat.eq_zero_or_pos (pos h j) with h0 | h0
      · exact Or.inl h0
      · right
        intro hlex
        obtain ⟨b0, b1, -, -, -, -⟩ := hcre (pos h j) h0 (by omega)
        have hlt := lt_of_lex hj hlex
        have := hmono (k * h + j + 1) (k * P (pos h j) + L (pos h j)) (by omega) (Nat.le_of_lt b0)
        rw [b1, hs1, a3] at this
        omega
    · have hlt : s (k * h + j) < c := by omega
      obtain ⟨b1, -, b3, b4⟩ := a4 hlt
      refine ⟨by omega, by rw [a2]; exact b1, Or.inr ?_⟩
      rw [a2, b3, b4]
      exact lex_irrefl
    · omega

end

end CFSG.KS.NKey

end
