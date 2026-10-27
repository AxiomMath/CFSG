module

public import CFSG.Certificates.Kernel.Spor.BfsReplay
public import Certificates.Data.GrSLitL34FactsCF23ONOutK3Data

public section

namespace CFSG.KS.Bfs3

open CFSG.KS.BfsReplay CFSG.ComponentClassification.SolMax.ONOut

structure R3 (step : Nat → Pt3 → Pt3) (k : Nat) (root : Pt3) (cnt : Nat) (T : Nat → Pt3)
    (par lab : Nat → Nat) (pos : Nat → Nat → Nat) : Prop where
  pos_cnt : 0 < cnt
  root_eq : T 0 = root
  par_zero : par 0 = 0
  lab_zero : lab 0 = 0
  inj : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b
  tree : ∀ i, 0 < i → i < cnt → par i < i ∧ lab i < k ∧ T i = step (lab i) (T (par i))
  order : ∀ i, 0 < i → i + 1 < cnt → LexLt (par i) (lab i) (par (i + 1)) (lab (i + 1))
  close : ∀ h < cnt, ∀ j < k, pos h j < cnt ∧ step j (T h) = T (pos h j) ∧
    (pos h j = 0 ∨ ¬ LexLt h j (par (pos h j)) (lab (pos h j)))

abbrev S3 := Array Nat × Array Nat × Array Pt3 × Std.HashSet Pt3

abbrev S3h := Array Nat × Array Nat × Array Pt3 × Std.HashSet Pt3 × Nat

@[expose] def inner3 (step : Nat → Pt3 → Pt3) (x : Pt3) (h l : Nat) (s : S3) :
    Id (ForInStep S3) :=
  if (!s.2.2.2.contains (step l x)) = true then
    pure (ForInStep.yield (s.1.push h, s.2.1.push l, s.2.2.1.push (step l x),
      s.2.2.2.insert (step l x)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def run3 (step : Nat → Pt3 → Pt3) (ng : Nat) (s : S3h) : S3 :=
  Id.run (forIn (List.range' 0 ng) (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
    (inner3 step s.2.2.1[s.2.2.2.2]! s.2.2.2.2))

@[expose] def outer3 (step : Nat → Pt3 → Pt3) (ng : Nat) (_t : Nat) (s : S3h) :
    Id (ForInStep S3h) :=
  if s.2.2.2.2 < s.2.2.1.size then
    pure (ForInStep.yield ((run3 step ng s).1, (run3 step ng s).2.1, (run3 step ng s).2.2.1,
      (run3 step ng s).2.2.2, s.2.2.2.2 + 1))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

@[expose] def init3 (root : Pt3) : S3h := (#[0], #[0], #[root], (∅ : Std.HashSet Pt3).insert root, 0)

theorem bfs3_eq (ng : Nat) (step : Nat → Pt3 → Pt3) (root : Pt3) (bound : Nat) :
    bfs3 ng step root bound =
      let s := Id.run (forIn (List.range' 0 bound) (init3 root) (outer3 step ng))
      (s.1, s.2.1, s.2.2.1) := by
  unfold bfs3
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

@[expose] def Inv3 (cnt : Nat) (T : Nat → Pt3) (par lab : Nat → Nat) (h j : Nat) (s : S3) : Prop :=
  s.2.2.1.size ≤ cnt ∧ s.1.size = s.2.2.1.size ∧ s.2.1.size = s.2.2.1.size ∧
    (∀ i < s.2.2.1.size, s.2.2.1[i]! = T i ∧ s.1[i]! = par i ∧ s.2.1[i]! = lab i) ∧
    (∀ u, s.2.2.2.contains u = true ↔ ∃ i < s.2.2.1.size, T i = u) ∧
    (∀ i < cnt, i < s.2.2.1.size ↔ (i = 0 ∨ LexLt (par i) (lab i) h j))

variable {step : Nat → Pt3 → Pt3} {k : Nat} {root : Pt3} {cnt : Nat} {T : Nat → Pt3}
  {par lab : Nat → Nat} {pos : Nat → Nat → Nat}

theorem R3.order_lt (R : R3 step k root cnt T par lab pos) {i i' : Nat} (h0 : 0 < i)
    (hi : i < i') (hi' : i' < cnt) : LexLt (par i) (lab i) (par i') (lab i') := by
  induction i' with
  | zero => omega
  | succ i' ih =>
    rcases Nat.lt_or_ge i i' with a | a
    · exact lex_trans (ih a (by omega)) (R.order i' (by omega) hi')
    · have e : i = i' := by omega
      subst e
      exact R.order i h0 hi'

theorem inv3_init (R : R3 step k root cnt T par lab pos) :
    Inv3 cnt T par lab 0 0 (#[0], #[0], #[root], (∅ : Std.HashSet Pt3).insert root) := by
  refine ⟨by simp; exact R.pos_cnt, rfl, rfl, fun i hi => ?_, fun u => ?_, fun i hi => ?_⟩
  · have : i = 0 := by simp at hi; omega
    subst this
    simp [R.root_eq, R.par_zero, R.lab_zero]
  · rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
    constructor
    · intro e
      exact ⟨0, by simp, by rw [R.root_eq]; exact beq_iff_eq.1 e⟩
    · rintro ⟨i, hi, e⟩
      have : i = 0 := by simp at hi; omega
      subst this
      rw [← e, R.root_eq]
      exact beq_self_eq_true _
  · simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
    unfold LexLt
    constructor
    · intro _
      exact Or.inl (by omega)
    · rintro (e | e)
      · omega
      · omega

theorem inner3_step (R : R3 step k root cnt T par lab pos) {h j : Nat} (hh : h < cnt)
    (hj : j < k) {s : S3} (hI : Inv3 cnt T par lab h j s) :
    ∃ s', inner3 step (T h) h j s = pure (ForInStep.yield s') ∧
      Inv3 cnt T par lab h (j + 1) s' ∧ s.2.2.1.size ≤ s'.2.2.1.size := by
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
    have hqs : ¬ q < s.2.2.1.size := by
      rw [hch q hq]
      rintro (e | e)
      · omega
      · rw [hpq, hlq] at e
        exact lex_irrefl e
    have hqm : q = s.2.2.1.size := by
      refine Nat.le_antisymm (Nat.le_of_not_lt fun hlt => ?_) (by omega)
      have hm0 : 0 < s.2.2.1.size := by
        have := (hch 0 R.pos_cnt).2 (Or.inl rfl)
        omega
      have hns : ¬ (s.2.2.1.size = 0 ∨ LexLt (par s.2.2.1.size) (lab s.2.2.1.size) h j) := by
        rw [← hch s.2.2.1.size (by omega)]
        exact Nat.lt_irrefl _
      have := R.order_lt hm0 hlt hq
      rw [hpq, hlq] at this
      unfold LexLt at this hns
      omega
    have hnc : s.2.2.2.contains (step j (T h)) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      obtain ⟨i, hi, e⟩ := (hK _).1 hc
      rw [hx] at e
      have := R.inj i (by omega) q hq e
      omega
    refine ⟨(s.1.push h, s.2.1.push j, s.2.2.1.push (step j (T h)),
      s.2.2.2.insert (step j (T h))), by simp [inner3, hnc], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp⟩
    · simp only [Array.size_push]
      omega
    · simp [hp]
    · simp [hl]
    · intro i hi
      simp only [Array.size_push] at hi
      rcases Nat.lt_or_ge i s.2.2.1.size with a | a
      · rw [push_lt a, push_lt (by omega : i < s.1.size), push_lt (by omega : i < s.2.1.size)]
        exact hget i a
      · have e : i = s.2.2.1.size := by omega
        subst e
        have e1 : (s.1.push h)[s.2.2.1.size]! = h := by rw [← hp]; exact push_eq
        have e2 : (s.2.1.push j)[s.2.2.1.size]! = j := by rw [← hl]; exact push_eq
        refine ⟨?_, ?_, ?_⟩
        · change (s.2.2.1.push (step j (T h)))[s.2.2.1.size]! = T s.2.2.1.size
          rw [push_eq, ← hqm, hx]
        · change (s.1.push h)[s.2.2.1.size]! = par s.2.2.1.size
          rw [e1, ← hqm, hpq]
        · change (s.2.1.push j)[s.2.2.1.size]! = lab s.2.2.1.size
          rw [e2, ← hqm, hlq]
    · intro u
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hK]
      simp only [Array.size_push]
      constructor
      · rintro (e | ⟨i, hi, e⟩)
        · exact ⟨s.2.2.1.size, by omega, by rw [← hqm, ← hx, e]⟩
        · exact ⟨i, by omega, e⟩
      · rintro ⟨i, hi, e⟩
        rcases Nat.lt_or_ge i s.2.2.1.size with a | a
        · exact Or.inr ⟨i, a, e⟩
        · have e' : i = s.2.2.1.size := by omega
          subst e'
          rw [← hqm, ← hx] at e
          exact Or.inl e
    · intro i hi
      simp only [Array.size_push]
      rw [hmove i hi, ← hch i hi]
      constructor
      · intro hlt
        rcases Nat.lt_or_ge i s.2.2.1.size with a | a
        · exact Or.inl a
        · have e : i = s.2.2.1.size := by omega
          subst e
          exact Or.inr ⟨by omega, by rw [← hqm]; exact hpq, by rw [← hqm]; exact hlq⟩
      · rintro (a | ⟨a0, a1, a2⟩)
        · omega
        · refine Classical.byContradiction fun hne => ?_
          have hgt : q < i := by omega
          have := R.order_lt hq0 hgt hi
          rw [hpq, hlq, a1, a2] at this
          exact lex_irrefl this
  · have hqs : q < s.2.2.1.size := by
      rw [hch q hq]
      rcases hor with e | e
      · exact Or.inl e
      · by_cases h0 : q = 0
        · exact Or.inl h0
        · right
          unfold LexLt at e ⊢
          have : ¬ (par q = h ∧ lab q = j) := fun e' => hnew ⟨by omega, e'.1, e'.2⟩
          omega
    have hc : s.2.2.2.contains (step j (T h)) = true := (hK _).2 ⟨q, hqs, by rw [hx]⟩
    refine ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), by simp [inner3, hc],
      ⟨hle, hp, hl, hget, hK, fun i hi => ?_⟩, Nat.le_refl _⟩
    rw [hmove i hi, ← hch i hi]
    constructor
    · exact Or.inl
    · rintro (a | ⟨a0, a1, a2⟩)
      · exact a
      · exfalso
        have e : T i = T q := by
          rw [← hx, (R.tree i a0 hi).2.2, a1, a2]
        have := R.inj i hi q hq e
        subst this
        exact hnew ⟨a0, a1, a2⟩

theorem inner3_spec (R : R3 step k root cnt T par lab pos) {h : Nat} (hh : h < cnt)
    {s : S3h} (hI : Inv3 cnt T par lab h 0 (s.1, s.2.1, s.2.2.1, s.2.2.2.1))
    (hhs : h < s.2.2.1.size) (hsh : s.2.2.2.2 = h) :
    Inv3 cnt T par lab (h + 1) 0 (run3 step k s) := by
  have hT : s.2.2.1[h]! = T h := (hI.2.2.2.1 h hhs).1
  unfold run3
  rw [hsh, hT]
  have := forIn_range'_yield k 0 (s.1, s.2.1, s.2.2.1, s.2.2.2.1) (inner3 step (T h) h)
    (fun j s' => Inv3 cnt T par lab h j s' ∧ s.2.2.1.size ≤ s'.2.2.1.size)
    (fun j hj s' hP => by
      rw [Nat.zero_add]
      obtain ⟨s'', e, hI', hle⟩ := inner3_step R hh hj hP.1
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

@[expose] def OInv (cnt : Nat) (T : Nat → Pt3) (par lab : Nat → Nat) (t : Nat) (s : S3h) : Prop :=
  s.2.2.2.2 = min t cnt ∧ Inv3 cnt T par lab (min t cnt) 0 (s.1, s.2.1, s.2.2.1, s.2.2.2.1)

theorem size_eq_of_inv (R : R3 step k root cnt T par lab pos) {s : S3}
    (hI : Inv3 cnt T par lab cnt 0 s) : s.2.2.1.size = cnt := by
  have := (hI.2.2.2.2.2 (cnt - 1) (by have := R.pos_cnt; omega)).2 (by
    by_cases h0 : cnt - 1 = 0
    · exact Or.inl h0
    · right
      left
      have := (R.tree (cnt - 1) (by omega) (by have := R.pos_cnt; omega)).1
      omega)
  have := hI.1
  omega

theorem outer3_spec (R : R3 step k root cnt T par lab pos) (bound : Nat) :
    OInv cnt T par lab bound
      (Id.run (forIn (List.range' 0 bound) (init3 root) (outer3 step k))) := by
  refine forIn_range'_yield bound 0 (init3 root) (outer3 step k) (OInv cnt T par lab)
    (fun t _ s hP => ?_) ⟨by simp [init3], by simpa [init3] using inv3_init R⟩
  obtain ⟨hh, hI⟩ := hP
  rcases Nat.lt_or_ge t cnt with a | a
  · rw [Nat.min_eq_left (Nat.le_of_lt a)] at hh hI
    have hhs : t < s.2.2.1.size := by
      rw [hI.2.2.2.2.2 t a]
      by_cases h0 : t = 0
      · exact Or.inl h0
      · right
        left
        exact (R.tree t (by omega) a).1
    refine ⟨_, by simp only [outer3, hh, hhs, if_true]; rfl, ?_, ?_⟩
    · change t + 1 = min (t + 1) cnt
      omega
    · rw [Nat.min_eq_left (by omega : t + 1 ≤ cnt)]
      exact inner3_spec R a hI hhs hh
  · rw [Nat.min_eq_right a] at hh hI
    have hns : ¬ s.2.2.2.2 < s.2.2.1.size := by
      rw [hh, size_eq_of_inv R hI]
      exact Nat.lt_irrefl _
    refine ⟨_, by simp only [outer3, hns, if_false]; rfl, ?_, ?_⟩
    · change s.2.2.2.2 = min (t + 1) cnt
      rw [hh]
      omega
    · rw [Nat.min_eq_right (by omega : cnt ≤ t + 1)]
      exact hI

theorem bfs3_replay (R : R3 step k root cnt T par lab pos) {bound : Nat} (hb : cnt ≤ bound) :
    bfs3 k step root bound = (Array.ofFn (n := cnt) fun i => par i.val,
      Array.ofFn (n := cnt) fun i => lab i.val, Array.ofFn (n := cnt) fun i => T i.val) := by
  have hO := outer3_spec R bound
  rw [bfs3_eq]
  generalize Id.run (forIn (List.range' 0 bound) (init3 root) (outer3 step k)) = s at hO
  obtain ⟨-, hI⟩ := hO
  rw [Nat.min_eq_right hb] at hI
  have hsz := size_eq_of_inv R hI
  obtain ⟨-, hp, hl, hget, -, -⟩ := hI
  have ext : ∀ {β : Type} [Inhabited β] (a : Array β) (f : Nat → β), a.size = cnt →
      (∀ i < cnt, a[i]! = f i) → a = Array.ofFn (n := cnt) fun i => f i.val :=
    fun a f ha hf => by
      apply Array.ext
      · simp [ha]
      · intro i h1 h2
        rw [Array.getElem_ofFn, ← getElem!_pos a i h1, hf i (by omega)]
  simp only at hsz hp hl hget ⊢
  rw [ext s.1 par (by omega) fun i hi => (hget i (by omega)).2.1,
    ext s.2.1 lab (by omega) fun i hi => (hget i (by omega)).2.2,
    ext s.2.2.1 T hsz fun i hi => (hget i (by omega)).1]

end CFSG.KS.Bfs3

end
