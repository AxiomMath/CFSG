module

public import Certificates.Data.Kernel.TwD5ReflK

public section

namespace CFSG.KC.TwD5R

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem notB_eq_true {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> decide

theorem allL_eq_true {α : Type} {l : List α} {p : α → Bool} :
    allL l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => exact ⟨fun _ a ha => (by cases ha), fun _ => rfl⟩
  | cons a t ih =>
    change andB (p a) (allL t p) = true ↔ _
    rw [List.forall_mem_cons, ← ih]
    exact andB_eq_true

theorem gens_sound {fx : Bool} {gens : List Nat} (h : allL gens (validH fx) = true) :
    ∀ g ∈ gens, validH fx g = true :=
  allL_eq_true.mp h

theorem repNOK_sound {fx : Bool} {reps : List Nat} (h : repNOK fx reps = true) :
    ∀ k ∈ reps, keyOK k = true ∧ reflInH fx k = false := by
  intro k hk
  obtain ⟨h1, h2⟩ := andB_eq_true.mp (allL_eq_true.mp h k hk)
  exact ⟨h1, notB_eq_true.mp h2⟩

theorem badOK_sound {fx : Bool} {gens : List Nat} {bad : List (Nat × List Nat)}
    (h : badOK fx gens bad = true) :
    ∀ e ∈ bad, badW fx gens [e.1] (Nat.succ (lenN gens)) e.2 = true := by
  intro e he
  have h1 := allL_eq_true.mp h e he
  rcases e with ⟨k, w⟩
  exact h1

theorem blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  simpa [Nat.blt_eq] using h

theorem lenN_eq {α : Type} (l : List α) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => exact congrArg Nat.succ ih

theorem testBit_packTab {l : List Nat} (hl : ∀ k ∈ l, k < 2 ^ 20) :
    ∀ r i, i < 20 → (packTab l).testBit (20 * r + i) = (l.getD r 0).testBit i := by
  induction l with
  | nil => intro r i _; simp [packTab]
  | cons k t ih =>
    intro r i hi
    have hk := hl k (List.mem_cons_self ..)
    have ht := ih (fun k hk => hl k (List.mem_cons_of_mem _ hk))
    change (k ||| (packTab t <<< 20)).testBit (20 * r + i) = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases r with
    | zero => simp; omega
    | succ r =>
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) (by omega)))]
      have e : 20 * (r + 1) + i - 20 = 20 * r + i := by omega
      have e' : 20 ≤ 20 * (r + 1) + i := by omega
      rw [e, ht r i hi]
      simp [e']

theorem getD_lt {l : List Nat} {B : Nat} (hl : ∀ k ∈ l, k < B) (hB : 0 < B) :
    ∀ r, l.getD r 0 < B := by
  induction l with
  | nil => intro r; simpa using hB
  | cons k t ih =>
    intro r
    cases r with
    | zero => simpa using hl k (List.mem_cons_self ..)
    | succ r => simpa using ih (fun k hk => hl k (List.mem_cons_of_mem _ hk)) r

theorem repAt_packTab {l : List Nat} (hl : ∀ k ∈ l, k < 2 ^ 20) (r : Nat) :
    repAt (packTab l) r = l.getD r 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((packTab l >>> (20 * r)) &&& (2 ^ 20 - 1)).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 20
  · simp [hi, testBit_packTab hl r i hi]
  · simp only [hi, decide_false, Bool.and_false]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (getD_lt hl (by omega) r)
      (Nat.pow_le_pow_right (by omega) (by omega)))).symm

theorem tabOK_sound {reps : List Nat} {repTab nrep : Nat} (h : tabOK reps repTab nrep = true) :
    nrep = reps.length ∧ ∀ r, r < nrep → repAt repTab r = reps.getD r 0 := by
  change andB (Nat.beq (packTab reps) repTab) (andB (Nat.beq (lenN reps) nrep)
    (andB (Nat.blt nrep 512) (allL reps fun k => Nat.blt k 531441))) = true at h
  obtain ⟨h1, h234⟩ := andB_eq_true.mp h
  obtain ⟨h2, h34⟩ := andB_eq_true.mp h234
  obtain ⟨-, h4⟩ := andB_eq_true.mp h34
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  rw [lenN_eq] at e2
  refine ⟨e2.symm, fun r _ => ?_⟩
  rw [← e1]
  exact repAt_packTab (fun k hk => by have := blt_true (allL_eq_true.mp h4 k hk); omega) r

theorem eqL_eq_true {l₁ l₂ : List Nat} (h : eqL l₁ l₂ = true) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b t => cases h
  | cons a t ih =>
    cases l₂ with
    | nil => cases h
    | cons b u =>
      change andB (Nat.beq a b) (eqL t u) = true at h
      obtain ⟨h1, h2⟩ := andB_eq_true.mp h
      rw [Nat.eq_of_beq_eq_true h1, ih h2]

theorem fstL_eq {β : Type} (l : List (Nat × β)) : fstL l = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    rcases e with ⟨k, w⟩
    exact congrArg (List.cons k) ih

theorem repsOK_sound {goods reps repsH : List Nat} {repsB : List (Nat × List Nat)}
    (h : repsOK goods reps repsH repsB = true) :
    reps = goods ++ (repsH ++ repsB.map Prod.fst) := by
  have e := eqL_eq_true h
  rw [fstL_eq] at e
  exact e

noncomputable def k1Loop (fx : Bool) (repTab nrep v : Nat) (st : Option (List Nat)) (N : Nat) :
    Option (List Nat) :=
  Nat.rec (motive := fun _ => Option (List Nat)) st (fun f ih => stepF fx repTab nrep v f ih) N

noncomputable def k1S (fx : Bool) (repTab nrep lo : Nat) (recs : List Nat) (i : Nat) :
    Option (List Nat) :=
  Nat.rec (motive := fun _ => Option (List Nat)) (some recs)
    (fun i ih => letN (Nat.add lo i) fun v =>
      Bool.rec (motive := fun _ => Option (List Nat)) ih (loopF fx repTab nrep v ih) (canon v)) i

theorem loopF_eq {fx : Bool} {repTab nrep v : Nat} {st : Option (List Nat)} :
    loopF fx repTab nrep v st = k1Loop fx repTab nrep v st 729 := by
  unfold loopF k1Loop
  rfl

theorem stepF_none {fx : Bool} {repTab nrep v f : Nat} : stepF fx repTab nrep v f none = none := by
  unfold stepF
  cases Nat.beq (dot v f) 1 <;> rfl

theorem k1Loop_none {fx : Bool} {repTab nrep v : Nat} :
    ∀ N, k1Loop fx repTab nrep v none N = none
  | 0 => rfl
  | N + 1 => by
    change stepF fx repTab nrep v N (k1Loop fx repTab nrep v none N) = none
    rw [k1Loop_none N]
    exact stepF_none

theorem k1Loop_ne_none {fx : Bool} {repTab nrep v : Nat} {st : Option (List Nat)} {j : Nat} :
    ∀ {N}, k1Loop fx repTab nrep v st (j + N) ≠ none → k1Loop fx repTab nrep v st j ≠ none
  | 0, h => h
  | N + 1, h => by
    apply k1Loop_ne_none (N := N)
    intro h0
    apply h
    change stepF fx repTab nrep v (j + N) (k1Loop fx repTab nrep v st (j + N)) = none
    rw [h0]
    exact stepF_none

theorem k1S_ne_none {fx : Bool} {repTab nrep lo : Nat} {recs : List Nat} {j : Nat} :
    ∀ {N}, k1S fx repTab nrep lo recs (j + N) ≠ none → k1S fx repTab nrep lo recs j ≠ none
  | 0, h => h
  | N + 1, h => by
    apply k1S_ne_none (N := N)
    intro h0
    apply h
    change Bool.rec (motive := fun _ => Option (List Nat)) (k1S fx repTab nrep lo recs (j + N))
      (loopF fx repTab nrep (Nat.add lo (j + N)) (k1S fx repTab nrep lo recs (j + N)))
      (canon (Nat.add lo (j + N))) = none
    rw [h0, loopF_eq, k1Loop_none]
    cases canon (Nat.add lo (j + N)) <;> rfl

theorem stepF_some {fx : Bool} {repTab nrep v f : Nat} {l : List Nat} (hd : dot v f = 1)
    (h : stepF fx repTab nrep v f (some l) ≠ none) :
    ∃ rec tl, l = rec :: tl ∧ recOK fx repTab nrep v f rec = true := by
  have hb : Nat.beq (dot v f) 1 = true := by rw [hd]; rfl
  unfold stepF at h
  rw [hb] at h
  cases l with
  | nil => exact (h rfl).elim
  | cons rec tl =>
    refine ⟨rec, tl, rfl, ?_⟩
    change Bool.rec (motive := fun _ => Option (List Nat)) none (some tl)
      (recOK fx repTab nrep v f rec) ≠ none at h
    cases hr : recOK fx repTab nrep v f rec
    · rw [hr] at h
      exact (h rfl).elim
    · rfl

theorem k1OK_sound {fx : Bool} {repTab nrep lo n : Nat} {recs : List Nat}
    (h : k1OK fx repTab nrep lo n recs = true) {v f : Nat} (hlo : lo ≤ v) (hv : v < lo + n)
    (hcv : canon v = true) (hf : f < 729) (hd : dot v f = 1) :
    ∃ r hc, r < nrep ∧ validH fx hc = true ∧ canonKey (act hc v) (act hc f) = repAt repTab r := by
  have hS : k1S fx repTab nrep lo recs n ≠ none := by
    intro h0
    change Option.rec (motive := fun _ => Bool) false
      (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
      (k1S fx repTab nrep lo recs n) = true at h
    rw [h0] at h
    cases h
  obtain ⟨i, rfl⟩ : ∃ i, v = lo + i := ⟨v - lo, by omega⟩
  have e1 : i + 1 + (n - (i + 1)) = n := by omega
  have h1 : k1S fx repTab nrep lo recs (i + 1) ≠ none :=
    k1S_ne_none (N := n - (i + 1)) (by rw [e1]; exact hS)
  change Bool.rec (motive := fun _ => Option (List Nat)) (k1S fx repTab nrep lo recs i)
    (loopF fx repTab nrep (lo + i) (k1S fx repTab nrep lo recs i)) (canon (lo + i)) ≠ none
    at h1
  rw [hcv, loopF_eq] at h1
  change k1Loop fx repTab nrep (lo + i) (k1S fx repTab nrep lo recs i) 729 ≠ none at h1
  have e2 : f + 1 + (728 - f) = 729 := by omega
  have h2 : k1Loop fx repTab nrep (lo + i) (k1S fx repTab nrep lo recs i) (f + 1) ≠ none :=
    k1Loop_ne_none (N := 728 - f) (by rw [e2]; exact h1)
  change stepF fx repTab nrep (lo + i) f
    (k1Loop fx repTab nrep (lo + i) (k1S fx repTab nrep lo recs i) f) ≠ none at h2
  cases h3 : k1Loop fx repTab nrep (lo + i) (k1S fx repTab nrep lo recs i) f with
  | none =>
    rw [h3, stepF_none] at h2
    exact (h2 rfl).elim
  | some l =>
    rw [h3] at h2
    obtain ⟨rec, tl, -, hr⟩ := stepF_some hd h2
    change andB (Nat.blt (rec &&& 511) nrep) (andB (validH fx (rec >>> 9))
      (Nat.beq (canonKey (act (rec >>> 9) (lo + i)) (act (rec >>> 9) f))
        (repAt repTab (rec &&& 511)))) = true at hr
    obtain ⟨hr1, hr⟩ := andB_eq_true.mp hr
    obtain ⟨hr2, hr3⟩ := andB_eq_true.mp hr
    exact ⟨rec &&& 511, rec >>> 9, blt_true hr1, hr2, Nat.eq_of_beq_eq_true hr3⟩

noncomputable def k12S (fx : Bool) (gens goods : List Nat) (ws : List (List Nat)) (m i : Nat) :
    Option (List (List Nat)) :=
  Nat.rec (motive := fun _ => Option (List (List Nat))) (some ws)
    (fun i ih => letN (Nat.div i m) fun c => letN (Nat.mod i m) fun c2 =>
      Bool.rec (motive := fun _ => Option (List (List Nat)))
        (Option.rec (motive := fun _ => Option (List (List Nat))) none
          (fun l => List.rec (motive := fun _ => Option (List (List Nat))) none
            (fun w tl _ => Bool.rec (motive := fun _ => Option (List (List Nat))) none (some tl)
              (badW fx gens [getN goods c, getN goods c2] (Nat.add (lenN gens) 2) w)) l) ih)
        ih (Nat.beq c c2)) i

theorem k12S_ne_none {fx : Bool} {gens goods : List Nat} {ws : List (List Nat)} {m j : Nat} :
    ∀ {N}, k12S fx gens goods ws m (j + N) ≠ none → k12S fx gens goods ws m j ≠ none
  | 0, h => h
  | N + 1, h => by
    apply k12S_ne_none (N := N)
    intro h0
    apply h
    change Bool.rec (motive := fun _ => Option (List (List Nat)))
      (Option.rec (motive := fun _ => Option (List (List Nat))) none
        (fun l => List.rec (motive := fun _ => Option (List (List Nat))) none
          (fun w tl _ => Bool.rec (motive := fun _ => Option (List (List Nat))) none (some tl)
            (badW fx gens [getN goods ((j + N) / m), getN goods ((j + N) % m)]
              (Nat.add (lenN gens) 2) w)) l) (k12S fx gens goods ws m (j + N)))
      (k12S fx gens goods ws m (j + N)) (Nat.beq ((j + N) / m) ((j + N) % m)) = none
    rw [h0]
    cases Nat.beq ((j + N) / m) ((j + N) % m) <;> rfl

theorem k12S_mem {fx : Bool} {gens goods : List Nat} {ws : List (List Nat)} {m : Nat} :
    ∀ {i l}, k12S fx gens goods ws m i = some l → ∀ x ∈ l, x ∈ ws
  | 0, l, h, x, hx => by
    change some ws = some l at h
    cases h
    exact hx
  | i + 1, l, h, x, hx => by
    change Bool.rec (motive := fun _ => Option (List (List Nat)))
      (Option.rec (motive := fun _ => Option (List (List Nat))) none
        (fun l => List.rec (motive := fun _ => Option (List (List Nat))) none
          (fun w tl _ => Bool.rec (motive := fun _ => Option (List (List Nat))) none (some tl)
            (badW fx gens [getN goods (i / m), getN goods (i % m)]
              (Nat.add (lenN gens) 2) w)) l) (k12S fx gens goods ws m i))
      (k12S fx gens goods ws m i) (Nat.beq (i / m) (i % m)) = some l at h
    cases hb : Nat.beq (i / m) (i % m)
    · rw [hb] at h
      cases h2 : k12S fx gens goods ws m i with
      | none =>
        rw [h2] at h
        cases h
      | some l' =>
        rw [h2] at h
        cases l' with
        | nil => cases h
        | cons w tl =>
          change Bool.rec (motive := fun _ => Option (List (List Nat))) none (some tl)
            (badW fx gens [getN goods (i / m), getN goods (i % m)] (Nat.add (lenN gens) 2) w)
            = some l at h
          cases hw : badW fx gens [getN goods (i / m), getN goods (i % m)] (Nat.add (lenN gens) 2) w
          · rw [hw] at h
            cases h
          · rw [hw] at h
            cases h
            exact k12S_mem h2 x (List.mem_cons_of_mem _ hx)
    · rw [hb] at h
      exact k12S_mem h x hx

theorem k12OK_sound {fx : Bool} {gens goods : List Nat} {ws : List (List Nat)}
    (h : k12OK fx gens goods ws = true) {c c' : Nat} (hc : c < goods.length)
    (hc' : c' < goods.length) (hne : c ≠ c') :
    ∃ w ∈ ws, badW fx gens [getN goods c, getN goods c'] (Nat.add (lenN gens) 2) w = true := by
  rw [← lenN_eq] at hc hc'
  generalize hm : lenN goods = m at hc hc'
  have hS : k12S fx gens goods ws m (m * m) ≠ none := by
    intro h0
    change Option.rec (motive := fun _ => Bool) false
      (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
      (k12S fx gens goods ws (lenN goods) (lenN goods * lenN goods)) = true at h
    rw [hm, h0] at h
    cases h
  have hm0 : 0 < m := by omega
  have hdiv : (m * c + c') / m = c := by
    rw [Nat.mul_add_div hm0, Nat.div_eq_of_lt hc', Nat.add_zero]
  have hmod : (m * c + c') % m = c' := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc']
  have hlt : m * c + c' + 1 ≤ m * m := by
    have := Nat.mul_le_mul_left m (Nat.succ_le_of_lt hc)
    rw [Nat.mul_succ] at this
    omega
  have e1 : m * c + c' + 1 + (m * m - (m * c + c' + 1)) = m * m := by omega
  have h1 : k12S fx gens goods ws m (m * c + c' + 1) ≠ none :=
    k12S_ne_none (N := m * m - (m * c + c' + 1)) (by rw [e1]; exact hS)
  change Bool.rec (motive := fun _ => Option (List (List Nat)))
      (Option.rec (motive := fun _ => Option (List (List Nat))) none
        (fun l => List.rec (motive := fun _ => Option (List (List Nat))) none
          (fun w tl _ => Bool.rec (motive := fun _ => Option (List (List Nat))) none (some tl)
            (badW fx gens [getN goods ((m * c + c') / m), getN goods ((m * c + c') % m)]
              (Nat.add (lenN gens) 2) w)) l) (k12S fx gens goods ws m (m * c + c')))
      (k12S fx gens goods ws m (m * c + c'))
      (Nat.beq ((m * c + c') / m) ((m * c + c') % m)) ≠ none at h1
  have hb : Nat.beq c c' = false := by
    cases hb : Nat.beq c c'
    · rfl
    · exact (hne (Nat.eq_of_beq_eq_true hb)).elim
  rw [hdiv, hmod, hb] at h1
  cases h2 : k12S fx gens goods ws m (m * c + c') with
  | none =>
    rw [h2] at h1
    exact (h1 rfl).elim
  | some l =>
    rw [h2] at h1
    cases l with
    | nil => exact (h1 rfl).elim
    | cons w tl =>
      change Bool.rec (motive := fun _ => Option (List (List Nat))) none (some tl)
        (badW fx gens [getN goods c, getN goods c'] (Nat.add (lenN gens) 2) w) ≠ none at h1
      refine ⟨w, k12S_mem h2 w (List.mem_cons_self ..), ?_⟩
      cases hw : badW fx gens [getN goods c, getN goods c'] (Nat.add (lenN gens) 2) w
      · rw [hw] at h1
        exact (h1 rfl).elim
      · rfl

noncomputable def incrS (l : List (Nat × Nat)) : Option Nat :=
  List.rec (motive := fun _ => Option Nat) (some 531441)
    (fun e _ ih => Option.rec (motive := fun _ => Option Nat) none
      (fun nx => Prod.rec (motive := fun _ => Option Nat)
        (fun k _ => Bool.rec (motive := fun _ => Option Nat) none (some k) (Nat.blt k nx)) e) ih) l

theorem incrS_sound : ∀ (l : List (Nat × Nat)) {m : Nat}, incrS l = some m →
    (l.map Prod.fst).Pairwise (· < ·) ∧ ∀ k ∈ l.map Prod.fst, m ≤ k
  | [], _, _ => ⟨List.Pairwise.nil, fun _ h => by cases h⟩
  | (k, w) :: t, m, h => by
    change Option.rec (motive := fun _ => Option Nat) none
      (fun nx => Bool.rec (motive := fun _ => Option Nat) none (some k) (Nat.blt k nx))
      (incrS t) = some m at h
    cases ht : incrS t with
    | none => rw [ht] at h; cases h
    | some nx =>
      rw [ht] at h
      change Bool.rec (motive := fun _ => Option Nat) none (some k) (Nat.blt k nx) = some m at h
      obtain ⟨hp, hle⟩ := incrS_sound t ht
      cases hb : Nat.blt k nx with
      | false => rw [hb] at h; cases h
      | true =>
        rw [hb] at h
        cases h
        have hk : k < nx := blt_true hb
        change (k :: t.map Prod.fst).Pairwise (· < ·) ∧ ∀ a ∈ k :: t.map Prod.fst, k ≤ a
        refine ⟨List.Pairwise.cons (fun a ha => by have := hle a ha; omega) hp, fun a ha => ?_⟩
        rcases List.mem_cons.mp ha with rfl | ha
        · exact Nat.le_refl _
        · have := hle a ha
          omega

theorem testBit_maskL : ∀ (l : List (Nat × Nat)) (k : Nat),
    (maskL l).testBit k = true ↔ k ∈ l.map Prod.fst
  | [], k => by simp [maskL]
  | (a, b) :: t, k => by
    change ((1 <<< a) ||| maskL t).testBit k = true ↔ k ∈ a :: t.map Prod.fst
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      testBit_maskL t k, List.mem_cons]
    simp [eq_comm]

theorem inM_iff {M k : Nat} : inM M k = true ↔ M.testBit k = true := by
  change Nat.blt 0 (M &&& (1 <<< k)) = true ↔ _
  rw [Nat.one_shiftLeft, Nat.blt_eq]
  constructor
  · intro h
    cases hb : M.testBit k
    · exfalso
      have h0 : M &&& 2 ^ k = 0 := Nat.eq_of_testBit_eq fun i => by
        rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
        by_cases hi : k = i
        · subst hi
          simp [hb]
        · simp [hi]
      omega
    · rfl
  · intro h
    apply Nat.pos_iff_ne_zero.mpr
    intro h0
    have := Nat.testBit_and M (2 ^ k) k
    rw [h0, Nat.zero_testBit, h, Nat.testBit_two_pow_self] at this
    cases this

theorem incr_maskL_sound {l : List (Nat × Nat)} (h : incr l = true) :
    (l.map Prod.fst).Pairwise (· < ·) ∧ ∀ k, inM (maskL l) k = true ↔ k ∈ l.map Prod.fst := by
  change Option.rec (motive := fun _ => Bool) false (fun _ => true) (incrS l) = true at h
  cases hs : incrS l with
  | none => rw [hs] at h; cases h
  | some m => exact ⟨(incrS_sound l hs).1, fun k => inM_iff.trans (testBit_maskL l k)⟩

theorem lhOK_sound {fx : Bool} {gens reps : List Nat} {l : List (Nat × Nat)}
    (h : lhOK fx gens reps l = true) :
    (l.map Prod.fst).Pairwise (· < ·) ∧ (∀ k ∈ reps, k ∈ l.map Prod.fst) ∧
      ∀ e ∈ l, keyOK e.1 = true ∧ reflInH fx e.1 = true ∧
        ∀ g ∈ gens, canonKey (act g (e.1 / 729)) (act g (e.1 % 729)) ∈ l.map Prod.fst := by
  change andB (incr l) (andB (allL reps fun k => inM (maskL l) k)
    (allL l fun e => Prod.rec (motive := fun _ => Bool)
      (fun k _ => andB (keyOK k) (andB (reflInH fx k) (closedAt gens (maskL l) k))) e)) = true at h
  obtain ⟨h1, h23⟩ := andB_eq_true.mp h
  obtain ⟨h2, h3⟩ := andB_eq_true.mp h23
  obtain ⟨hp, hm⟩ := incr_maskL_sound h1
  refine ⟨hp, fun k hk => (hm k).mp (allL_eq_true.mp h2 k hk), fun e he => ?_⟩
  have h4 := allL_eq_true.mp h3 e he
  rcases e with ⟨k, w⟩
  change andB (keyOK k) (andB (reflInH fx k) (closedAt gens (maskL l) k)) = true at h4
  obtain ⟨h5, h67⟩ := andB_eq_true.mp h4
  obtain ⟨h6, h7⟩ := andB_eq_true.mp h67
  refine ⟨h5, h6, fun g hg => (hm _).mp ?_⟩
  change allL gens (fun g => inM (maskL l) (canonKey (act g (k / 729)) (act g (k % 729)))) = true
    at h7
  exact allL_eq_true.mp h7 g hg

theorem lgOK_sound {fx : Bool} {gens : List Nat} {gk : Nat} {l : List (Nat × Nat)}
    (h : lgOK fx gens gk l = true) :
    (l.map Prod.fst).Pairwise (· < ·) ∧ gk ∈ l.map Prod.fst ∧
      ∀ e ∈ l, keyOK e.1 = true ∧
        (∃ hc, validH fx hc = true ∧ canonKey (act hc (e.1 / 729)) (act hc (e.1 % 729)) = gk) ∧
        ∀ g ∈ gens, canonKey (act g (e.1 / 729)) (act g (e.1 % 729)) ∈ l.map Prod.fst := by
  change andB (incr l) (andB (inM (maskL l) gk)
    (allL l fun e => Prod.rec (motive := fun _ => Bool)
      (fun k w => andB (keyOK k) (andB (validH fx (Nat.land w 16777215))
        (andB (Nat.beq (canonKey (act (Nat.land w 16777215) (k / 729))
          (act (Nat.land w 16777215) (k % 729))) gk) (closedAt gens (maskL l) k)))) e)) = true at h
  obtain ⟨h1, h23⟩ := andB_eq_true.mp h
  obtain ⟨h2, h3⟩ := andB_eq_true.mp h23
  obtain ⟨hp, hm⟩ := incr_maskL_sound h1
  refine ⟨hp, (hm gk).mp h2, fun e he => ?_⟩
  have h4 := allL_eq_true.mp h3 e he
  rcases e with ⟨k, w⟩
  change andB (keyOK k) (andB (validH fx (Nat.land w 16777215))
    (andB (Nat.beq (canonKey (act (Nat.land w 16777215) (k / 729))
      (act (Nat.land w 16777215) (k % 729))) gk) (closedAt gens (maskL l) k))) = true at h4
  obtain ⟨h5, h4⟩ := andB_eq_true.mp h4
  obtain ⟨h6, h4⟩ := andB_eq_true.mp h4
  obtain ⟨h7, h8⟩ := andB_eq_true.mp h4
  refine ⟨h5, ⟨Nat.land w 16777215, h6, Nat.eq_of_beq_eq_true h7⟩, fun g hg => (hm _).mp ?_⟩
  change allL gens (fun g => inM (maskL l) (canonKey (act g (k / 729)) (act g (k % 729)))) = true
    at h8
  exact allL_eq_true.mp h8 g hg

theorem dg_eq' (x j : Nat) : dg x j = x / 3 ^ j % 3 := rfl

theorem dg_lt3 (x j : Nat) : dg x j < 3 := Nat.mod_lt _ (by omega)

theorem dg_sum6 {c0 c1 c2 c3 c4 c5 : Nat} (h0 : c0 < 3) (h1 : c1 < 3) (h2 : c2 < 3) (h3 : c3 < 3)
    (h4 : c4 < 3) (h5 : c5 < 3) :
    dg (c0 + 3 * c1 + 9 * c2 + 27 * c3 + 81 * c4 + 243 * c5) 0 = c0 ∧
    dg (c0 + 3 * c1 + 9 * c2 + 27 * c3 + 81 * c4 + 243 * c5) 1 = c1 ∧
    dg (c0 + 3 * c1 + 9 * c2 + 27 * c3 + 81 * c4 + 243 * c5) 2 = c2 ∧
    dg (c0 + 3 * c1 + 9 * c2 + 27 * c3 + 81 * c4 + 243 * c5) 3 = c3 ∧
    dg (c0 + 3 * c1 + 9 * c2 + 27 * c3 + 81 * c4 + 243 * c5) 4 = c4 ∧
    dg (c0 + 3 * c1 + 9 * c2 + 27 * c3 + 81 * c4 + 243 * c5) 5 = c5 := by
  simp only [dg_eq', Nat.reducePow]
  omega

theorem eq_of_dg {x y : Nat} (hx : x < 729) (hy : y < 729) (h : ∀ j, j < 6 → dg x j = dg y j) :
    x = y := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 4 (by omega)
  have h5 := h 5 (by omega)
  simp only [dg_eq', Nat.reducePow] at h0 h1 h2 h3 h4 h5
  omega

theorem negV_eq' (x : Nat) :
    negV x = 2 * dg x 0 % 3 + 3 * (2 * dg x 1 % 3) + 9 * (2 * dg x 2 % 3) +
      27 * (2 * dg x 3 % 3) + 81 * (2 * dg x 4 % 3) + 243 * (2 * dg x 5 % 3) := by
  change 0 + 2 * dg x 0 % 3 * 1 + 2 * dg x 1 % 3 * 3 + 2 * dg x 2 % 3 * 9 +
    2 * dg x 3 % 3 * 27 + 2 * dg x 4 % 3 * 81 + 2 * dg x 5 % 3 * 243 = _
  omega

theorem negV_lt' (x : Nat) : negV x < 729 := by
  rw [negV_eq']
  omega

theorem dg_negV (x j : Nat) (hj : j < 6) : dg (negV x) j = 2 * dg x j % 3 := by
  have m : ∀ i, 2 * dg x i % 3 < 3 := fun i => Nat.mod_lt _ (by omega)
  have h := dg_sum6 (m 0) (m 1) (m 2) (m 3) (m 4) (m 5)
  rw [negV_eq']
  match j, hj with
  | 0, _ => exact h.1
  | 1, _ => exact h.2.1
  | 2, _ => exact h.2.2.1
  | 3, _ => exact h.2.2.2.1
  | 4, _ => exact h.2.2.2.2.1
  | 5, _ => exact h.2.2.2.2.2

theorem negV_negV (x : Nat) (hx : x < 729) : negV (negV x) = x := by
  apply eq_of_dg (negV_lt' _) hx
  intro j hj
  rw [dg_negV _ j hj, dg_negV _ j hj]
  have := dg_lt3 x j
  omega

theorem mod3_neg_mul : ∀ a, a < 3 → ∀ b, b < 3 → 2 * a % 3 * b % 3 = 2 * (a * b) % 3 := by
  decide

theorem dot_negV (x f : Nat) : dot (negV x) f = 2 * dot x f % 3 := by
  change (dg (negV x) 0 * dg f 0 + dg (negV x) 1 * dg f 1 + (dg (negV x) 2 * dg f 2 +
    dg (negV x) 3 * dg f 3) + (dg (negV x) 4 * dg f 4 + dg (negV x) 5 * dg f 5)) % 3 =
    2 * ((dg x 0 * dg f 0 + dg x 1 * dg f 1 + (dg x 2 * dg f 2 +
    dg x 3 * dg f 3) + (dg x 4 * dg f 4 + dg x 5 * dg f 5)) % 3) % 3
  rw [dg_negV x 0 (by omega), dg_negV x 1 (by omega), dg_negV x 2 (by omega),
    dg_negV x 3 (by omega), dg_negV x 4 (by omega), dg_negV x 5 (by omega)]
  have e : ∀ i, 2 * dg x i % 3 * dg f i % 3 = 2 * (dg x i * dg f i) % 3 :=
    fun i => mod3_neg_mul _ (dg_lt3 x i) _ (dg_lt3 f i)
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  have e4 := e 4
  have e5 := e 5
  generalize 2 * dg x 0 % 3 * dg f 0 = q0 at *
  generalize 2 * dg x 1 % 3 * dg f 1 = q1 at *
  generalize 2 * dg x 2 % 3 * dg f 2 = q2 at *
  generalize 2 * dg x 3 % 3 * dg f 3 = q3 at *
  generalize 2 * dg x 4 % 3 * dg f 4 = q4 at *
  generalize 2 * dg x 5 % 3 * dg f 5 = q5 at *
  generalize dg x 0 * dg f 0 = p0 at *
  generalize dg x 1 * dg f 1 = p1 at *
  generalize dg x 2 * dg f 2 = p2 at *
  generalize dg x 3 * dg f 3 = p3 at *
  generalize dg x 4 * dg f 4 = p4 at *
  generalize dg x 5 * dg f 5 = p5 at *
  omega

theorem reflV_eq' (key x : Nat) :
    reflV key x = (dg x 0 + dot x (key % 729) * dg (key / 729) 0) % 3 +
      3 * ((dg x 1 + dot x (key % 729) * dg (key / 729) 1) % 3) +
      9 * ((dg x 2 + dot x (key % 729) * dg (key / 729) 2) % 3) +
      27 * ((dg x 3 + dot x (key % 729) * dg (key / 729) 3) % 3) +
      81 * ((dg x 4 + dot x (key % 729) * dg (key / 729) 4) % 3) +
      243 * ((dg x 5 + dot x (key % 729) * dg (key / 729) 5) % 3) := by
  change 0 + (dg x 0 + dot x (key % 729) * dg (key / 729) 0) % 3 * 1 +
    (dg x 1 + dot x (key % 729) * dg (key / 729) 1) % 3 * 3 +
    (dg x 2 + dot x (key % 729) * dg (key / 729) 2) % 3 * 9 +
    (dg x 3 + dot x (key % 729) * dg (key / 729) 3) % 3 * 27 +
    (dg x 4 + dot x (key % 729) * dg (key / 729) 4) % 3 * 81 +
    (dg x 5 + dot x (key % 729) * dg (key / 729) 5) % 3 * 243 = _
  omega

theorem dg_reflV (key x j : Nat) (hj : j < 6) :
    dg (reflV key x) j = (dg x j + dot x (key % 729) * dg (key / 729) j) % 3 := by
  have m : ∀ i, (dg x i + dot x (key % 729) * dg (key / 729) i) % 3 < 3 :=
    fun i => Nat.mod_lt _ (by omega)
  have h := dg_sum6 (m 0) (m 1) (m 2) (m 3) (m 4) (m 5)
  rw [reflV_eq']
  match j, hj with
  | 0, _ => exact h.1
  | 1, _ => exact h.2.1
  | 2, _ => exact h.2.2.1
  | 3, _ => exact h.2.2.2.1
  | 4, _ => exact h.2.2.2.2.1
  | 5, _ => exact h.2.2.2.2.2

theorem reflV_lt (key x : Nat) : reflV key x < 729 := by
  rw [reflV_eq']
  have m : ∀ i, (dg x i + dot x (key % 729) * dg (key / 729) i) % 3 < 3 :=
    fun i => Nat.mod_lt _ (by omega)
  have := m 0
  have := m 1
  have := m 2
  have := m 3
  have := m 4
  have := m 5
  omega

theorem mod3_refl : ∀ a, a < 3 → ∀ t, t < 3 → ∀ b, b < 3 →
    (2 * a % 3 + 2 * t % 3 * b) % 3 = 2 * ((a + t * b) % 3) % 3 := by
  decide

theorem reflV_negV (key x : Nat) : reflV key (negV x) = negV (reflV key x) := by
  apply eq_of_dg (reflV_lt _ _) (negV_lt' _)
  intro j hj
  simp only [dg_reflV _ _ j hj, dg_negV _ j hj, dot_negV]
  exact mod3_refl _ (dg_lt3 x j) _ (Nat.mod_lt _ (by omega)) _ (dg_lt3 _ j)

theorem lanes_nodup_b : (List.range 6).all (fun a => (List.range 6).all fun b =>
    (List.range 6).all fun c => (List.range 6).all fun d => (List.range 6).all fun e =>
      (((1 <<< 0 ||| 1 <<< a) ||| (1 <<< b ||| 1 <<< c)) ||| (1 <<< d ||| 1 <<< e) != 63) ||
      (0 != a && 0 != b && 0 != c && 0 != d && 0 != e && a != b && a != c && a != d && a != e &&
        b != c && b != d && b != e && c != d && c != e && d != e)) = true := by
  decide +kernel

theorem lanes_nodup {a b c d e : Nat} (ha : a < 6) (hb : b < 6) (hc : c < 6) (hd : d < 6)
    (he : e < 6)
    (h : ((1 <<< 0 ||| 1 <<< a) ||| (1 <<< b ||| 1 <<< c)) ||| (1 <<< d ||| 1 <<< e) = 63) :
    [0, a, b, c, d, e].Nodup := by
  have h1 := lanes_nodup_b
  simp only [List.all_eq_true, List.mem_range] at h1
  have h1 := h1 a ha b hb c hc d hd e he
  rw [h] at h1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, and_true, or_false,
    not_false_eq_true]
  simp at h1
  omega

theorem validH_lanes {fx : Bool} {g : Nat} (h : validH fx g = true) :
    (∀ i, (lane g 0 = i ∨ lane g 1 = i ∨ lane g 2 = i ∨ lane g 3 = i ∨ lane g 4 = i ∨
      lane g 5 = i) ↔ i < 6) ∧
    [lane g 0, lane g 1, lane g 2, lane g 3, lane g 4, lane g 5].Nodup := by
  obtain ⟨-, h⟩ := andB_eq_true.mp h
  obtain ⟨h0, h⟩ := andB_eq_true.mp h
  obtain ⟨h, -⟩ := andB_eq_true.mp h
  have hOR' := Nat.eq_of_beq_eq_true h
  have h0 := Nat.eq_of_beq_eq_true h0
  change ((1 <<< lane g 0 ||| 1 <<< lane g 1) ||| (1 <<< lane g 2 ||| 1 <<< lane g 3)) |||
    (1 <<< lane g 4 ||| 1 <<< lane g 5) = 63 at hOR'
  have hOR : ((1 <<< lane g 0 ||| 1 <<< lane g 1) ||| (1 <<< lane g 2 ||| 1 <<< lane g 3)) |||
    (1 <<< lane g 4 ||| 1 <<< lane g 5) = 2 ^ 6 - 1 := hOR'
  have cover : ∀ i, (lane g 0 = i ∨ lane g 1 = i ∨ lane g 2 = i ∨ lane g 3 = i ∨ lane g 4 = i ∨
      lane g 5 = i) ↔ i < 6 := by
    intro i
    have := congrArg (fun n => Nat.testBit n i) hOR
    simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
      Nat.testBit_two_pow_sub_one] at this
    have := Bool.eq_iff_iff.mp this
    simp only [Bool.or_eq_true, decide_eq_true_eq, or_assoc] at this
    exact this
  refine ⟨cover, ?_⟩
  rw [h0]
  have hl : ∀ j, lane g j = lane g j := fun _ => rfl
  have l1 := (cover _).mp (Or.inr (Or.inl (hl 1)))
  have l2 := (cover _).mp (Or.inr (Or.inr (Or.inl (hl 2))))
  have l3 := (cover _).mp (Or.inr (Or.inr (Or.inr (Or.inl (hl 3)))))
  have l4 := (cover _).mp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hl 4))))))
  have l5 := (cover _).mp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hl 5))))))
  rw [h0] at hOR'
  exact lanes_nodup l1 l2 l3 l4 l5 hOR'

theorem dg_add_pow {a c l : Nat} (hl : l < 6) (hc : c < 3) (ha : a < 729) (h0 : dg a l = 0) :
    a + c * 3 ^ l < 729 ∧ ∀ i, i < 6 → dg (a + c * 3 ^ l) i = if i = l then c else dg a i := by
  refine ⟨?_, fun i hi => ?_⟩
  · rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dg_eq', Nat.reducePow] at h0 ⊢ <;> omega
  · rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dg_eq', Nat.reducePow] at h0 ⊢ <;>
      simp <;> omega

def sum3 : List (Nat × Nat) → Nat
  | [] => 0
  | (c, l) :: t => sum3 t + c * 3 ^ l

theorem dg_sum3 : ∀ (ps : List (Nat × Nat)), (∀ p ∈ ps, p.1 < 3 ∧ p.2 < 6) →
    (ps.map Prod.snd).Nodup → sum3 ps < 729 ∧ (∀ p ∈ ps, dg (sum3 ps) p.2 = p.1) ∧
      ∀ i, i < 6 → i ∉ ps.map Prod.snd → dg (sum3 ps) i = 0
  | [], _, _ => by
    refine ⟨by change 0 < 729; omega, ⟨fun _ h => absurd h List.not_mem_nil, fun i _ _ => ?_⟩⟩
    change 0 / 3 ^ i % 3 = 0
    simp
  | (c, l) :: t, hb, hn => by
    rw [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hlt, hnt⟩ := hn
    obtain ⟨h1, h2, h3⟩ := dg_sum3 t (fun p hp => hb p (List.mem_cons_of_mem _ hp)) hnt
    have hcl := hb (c, l) (List.mem_cons_self ..)
    obtain ⟨b1, b2⟩ := dg_add_pow hcl.2 hcl.1 h1 (h3 l hcl.2 hlt)
    change sum3 t + c * 3 ^ l < 729 ∧ (∀ p ∈ (c, l) :: t, dg (sum3 t + c * 3 ^ l) p.2 = p.1) ∧
      ∀ i, i < 6 → i ∉ ((c, l) :: t).map Prod.snd → dg (sum3 t + c * 3 ^ l) i = 0
    refine ⟨b1, fun p hp => ?_, fun i hi hni => ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · simp [b2 _ hcl.2]
      · have hpl : p.2 ≠ l := fun e => hlt (by rw [← e]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
        simp [b2 _ (hb p (List.mem_cons_of_mem _ hp)).2, hpl, h2 p hp]
    · rw [List.map_cons, List.mem_cons, not_or] at hni
      simp [b2 _ hi, hni.1, h3 i hi hni.2]

theorem term_eq_pow (g x j : Nat) : term g x j = dg x j * (1 + sbit g j) % 3 * 3 ^ lane g j :=
  rfl

theorem act_eq_sum3 (g x : Nat) : act g x = sum3 [(dg x 0 * (1 + sbit g 0) % 3, lane g 0),
    (dg x 1 * (1 + sbit g 1) % 3, lane g 1), (dg x 2 * (1 + sbit g 2) % 3, lane g 2),
    (dg x 3 * (1 + sbit g 3) % 3, lane g 3), (dg x 4 * (1 + sbit g 4) % 3, lane g 4),
    (dg x 5 * (1 + sbit g 5) % 3, lane g 5)] := by
  change ((term g x 0 + term g x 1) + (term g x 2 + term g x 3)) + (term g x 4 + term g x 5) = _
  simp only [sum3, term_eq_pow]
  omega

theorem dg_act_lane {fx : Bool} {g : Nat} (hg : validH fx g = true) (x : Nat) :
    act g x < 729 ∧ ∀ j, j < 6 → dg (act g x) (lane g j) = dg x j * (1 + sbit g j) % 3 := by
  obtain ⟨cover, hnd⟩ := validH_lanes hg
  have hl : ∀ j, j < 6 → lane g j < 6 := fun j hj => by
    match j, hj with
    | 0, _ => exact (cover _).mp (Or.inl rfl)
    | 1, _ => exact (cover _).mp (Or.inr (Or.inl rfl))
    | 2, _ => exact (cover _).mp (Or.inr (Or.inr (Or.inl rfl)))
    | 3, _ => exact (cover _).mp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | 4, _ => exact (cover _).mp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | 5, _ => exact (cover _).mp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hc : ∀ j, dg x j * (1 + sbit g j) % 3 < 3 := fun j => Nat.mod_lt _ (by omega)
  obtain ⟨h1, h2, -⟩ := dg_sum3 [(dg x 0 * (1 + sbit g 0) % 3, lane g 0),
    (dg x 1 * (1 + sbit g 1) % 3, lane g 1), (dg x 2 * (1 + sbit g 2) % 3, lane g 2),
    (dg x 3 * (1 + sbit g 3) % 3, lane g 3), (dg x 4 * (1 + sbit g 4) % 3, lane g 4),
    (dg x 5 * (1 + sbit g 5) % 3, lane g 5)] (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨hc _, hl _ (by omega)⟩) (by simpa using hnd)
  rw [act_eq_sum3]
  refine ⟨h1, fun j hj => ?_⟩
  have h2' := fun k => h2 (dg x k * (1 + sbit g k) % 3, lane g k)
  match j, hj with
  | 0, _ => exact h2' 0 (by simp)
  | 1, _ => exact h2' 1 (by simp)
  | 2, _ => exact h2' 2 (by simp)
  | 3, _ => exact h2' 3 (by simp)
  | 4, _ => exact h2' 4 (by simp)
  | 5, _ => exact h2' 5 (by simp)

theorem mod3_act : ∀ a, a < 3 → ∀ s, s < 2 →
    2 * a % 3 * (1 + s) % 3 = 2 * (a * (1 + s) % 3) % 3 := by
  decide

theorem act_negV {fx : Bool} {g : Nat} (hg : validH fx g = true) (y : Nat) :
    act g (negV y) = negV (act g y) := by
  obtain ⟨cover, -⟩ := validH_lanes hg
  obtain ⟨b1, d1⟩ := dg_act_lane hg (negV y)
  obtain ⟨-, d2⟩ := dg_act_lane hg y
  have key : ∀ j, j < 6 → lane g j < 6 →
      dg (act g (negV y)) (lane g j) = dg (negV (act g y)) (lane g j) := by
    intro j hj hlj
    rw [d1 j hj, dg_negV y j hj, dg_negV _ _ hlj, d2 j hj]
    exact mod3_act _ (dg_lt3 y j) _ (Nat.lt_of_le_of_lt Nat.and_le_right (by omega))
  apply eq_of_dg b1 (negV_lt' _)
  intro i hi
  rcases (cover i).mpr hi with h | h | h | h | h | h <;> subst h <;> exact key _ (by omega) hi

theorem getN_mem : ∀ (l : List Nat) (i : Nat), i < l.length → getN l i ∈ l
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: t, 0, _ => List.mem_cons_self ..
  | a :: t, i + 1, h => List.mem_cons_of_mem _ (getN_mem t i (by simp at h; omega))

theorem applyL_negV {fx : Bool} {gens : List Nat} {gk : Nat}
    (hg : ∀ g ∈ gens, validH fx g = true) (g y : Nat) :
    applyL gens [gk] g (negV y) = negV (applyL gens [gk] g y) := by
  change Bool.rec (motive := fun _ => Nat) (reflV (getN [gk] (g - lenN gens)) (negV y))
      (act (getN gens g) (negV y)) (Nat.blt g (lenN gens)) =
    negV (Bool.rec (motive := fun _ => Nat) (reflV (getN [gk] (g - lenN gens)) y)
      (act (getN gens g) y) (Nat.blt g (lenN gens)))
  cases hb : Nat.blt g (lenN gens)
  · exact reflV_negV _ _
  · have := blt_true hb
    rw [lenN_eq] at this
    exact act_negV (hg _ (getN_mem gens g this)) y

noncomputable def reachF (gens refls : List Nat) (nl : Nat) (ow : List (Nat × (Nat × Nat)))
    (R : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun R => R)
    (fun e _ ih R => Prod.rec (motive := fun _ => Nat) (fun x yg => Prod.rec (motive := fun _ => Nat)
      (fun y g => letN (applyL gens refls g y) fun z =>
        Bool.rec (motive := fun _ => Nat) 0
          (ih (Nat.lor R (Nat.lor (Nat.shiftLeft 1 x) (Nat.shiftLeft 1 (negV x)))))
          (andB (inM R y) (andB (Nat.blt g nl) (andB (Nat.blt x 729)
            (orB (Nat.beq z x) (Nat.beq z (negV x))))))) yg) e) ow R

def ReachInv (gens refls : List Nat) (nl R : Nat) : Prop :=
  ∀ y, R.testBit y = true → ∃ w : List Nat, (∀ g ∈ w, g < nl) ∧
    (applyW gens refls w 1 = y ∨ applyW gens refls w 1 = negV y)

theorem orB_eq_true {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem reachF_inv {gens refls : List Nat} {nl : Nat}
    (hlin : ∀ g y, applyL gens refls g (negV y) = negV (applyL gens refls g y)) :
    ∀ (ow : List (Nat × (Nat × Nat))) (R : Nat), ReachInv gens refls nl R →
      ReachInv gens refls nl (reachF gens refls nl ow R)
  | [], _, hR => hR
  | (x, y, g) :: t, R, hR => by
    change ReachInv gens refls nl (Bool.rec (motive := fun _ => Nat) 0
      (reachF gens refls nl t (R ||| ((1 <<< x) ||| (1 <<< negV x))))
      (andB (inM R y) (andB (Nat.blt g nl) (andB (Nat.blt x 729)
        (orB (Nat.beq (applyL gens refls g y) x) (Nat.beq (applyL gens refls g y) (negV x)))))))
    cases hc : andB (inM R y) (andB (Nat.blt g nl) (andB (Nat.blt x 729)
        (orB (Nat.beq (applyL gens refls g y) x) (Nat.beq (applyL gens refls g y) (negV x)))))
    · intro y' hy'
      rw [Nat.zero_testBit] at hy'
      cases hy'
    · apply reachF_inv hlin t
      obtain ⟨c1, c⟩ := andB_eq_true.mp hc
      obtain ⟨c2, c⟩ := andB_eq_true.mp c
      obtain ⟨c3, c4⟩ := andB_eq_true.mp c
      have hx : x < 729 := blt_true c3
      obtain ⟨w, hw, hu⟩ := hR y (inM_iff.mp c1)
      have hz : applyL gens refls g y = x ∨ applyL gens refls g y = negV x := by
        rcases orB_eq_true.mp c4 with h | h
        · exact Or.inl (Nat.eq_of_beq_eq_true h)
        · exact Or.inr (Nat.eq_of_beq_eq_true h)
      have hv : applyW gens refls (g :: w) 1 = x ∨ applyW gens refls (g :: w) 1 = negV x := by
        change applyL gens refls g (applyW gens refls w 1) = x ∨
          applyL gens refls g (applyW gens refls w 1) = negV x
        rcases hu with hu | hu <;> rw [hu]
        · exact hz
        · rw [hlin]
          rcases hz with hz | hz <;> rw [hz]
          · exact Or.inr rfl
          · rw [negV_negV x hx]
            exact Or.inl rfl
      have hw' : ∀ g' ∈ g :: w, g' < nl := by
        intro g' hg'
        rcases List.mem_cons.mp hg' with rfl | hg'
        · exact blt_true c2
        · exact hw g' hg'
      intro y' hy'
      rw [Nat.testBit_or, Nat.testBit_or, Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow,
        Nat.testBit_two_pow] at hy'
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hy'
      rcases hy' with hy' | rfl | rfl
      · exact hR y' hy'
      · exact ⟨g :: w, hw', hv⟩
      · refine ⟨g :: w, hw', ?_⟩
        rw [negV_negV x hx]
        exact hv.symm

theorem reachM_sound {gens refls : List Nat} {nl : Nat}
    (hlin : ∀ g y, applyL gens refls g (negV y) = negV (applyL gens refls g y))
    (ow : List (Nat × (Nat × Nat))) : ReachInv gens refls nl (reachM gens refls nl ow) := by
  change ReachInv gens refls nl (reachF gens refls nl ow 6)
  apply reachF_inv hlin
  intro y hy
  have e6 : (6 : Nat) = 2 ^ 1 ||| 2 ^ 2 := rfl
  rw [e6, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow] at hy
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hy
  refine ⟨[], fun _ h => absurd h List.not_mem_nil, ?_⟩
  rcases hy with rfl | rfl
  · exact Or.inl rfl
  · refine Or.inr ?_
    change 1 = negV 2
    decide

noncomputable def planeN (j d N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun x ih => Nat.lor ih (Nat.shiftLeft (selN (Nat.beq (dg x j) d) 1 0) x)) N

theorem plane_eq (j d : Nat) : plane j d = planeN j d 729 := by
  unfold plane planeN
  rfl

theorem testBit_planeN (j d : Nat) :
    ∀ N y, (planeN j d N).testBit y = decide (y < N ∧ dg y j = d)
  | 0, y => by
    change Nat.testBit 0 y = _
    simp
  | N + 1, y => by
    change (planeN j d N ||| (selN (Nat.beq (dg N j) d) 1 0 <<< N)).testBit y = _
    rw [Nat.testBit_or, testBit_planeN j d N y]
    cases hb : Nat.beq (dg N j) d
    · have hne : dg N j ≠ d := fun h => by
        rw [h, Nat.beq_refl] at hb
        cases hb
      change (decide _ || (0 <<< N).testBit y) = _
      rw [Nat.zero_shiftLeft, Nat.zero_testBit, Bool.or_false]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
        · exact h
        · subst h
          exact absurd h2 hne
    · have he : dg N j = d := Nat.eq_of_beq_eq_true hb
      change (decide _ || (1 <<< N).testBit y) = _
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨by omega, h2⟩
        · exact ⟨by omega, he⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr h.symm

noncomputable def planesN (M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => Nat.lor ih (Nat.shiftLeft (Nat.lor (plane j 1) (Nat.shiftLeft (plane j 2) 729))
      (Nat.mul 1458 j))) M

theorem planes_eq : planes = planesN 6 := by
  unfold planes planesN
  rfl

theorem testBit_planesN : ∀ M j e y, e < 2 → y < 729 →
    (planesN M).testBit (1458 * j + 729 * e + y) = decide (j < M ∧ dg y j = e + 1)
  | 0, j, e, y, _, _ => by
    change Nat.testBit 0 _ = _
    simp
  | M + 1, j, e, y, he, hy => by
    change (planesN M ||| ((plane M 1 ||| (plane M 2 <<< 729)) <<< (1458 * M))).testBit _ = _
    rw [Nat.testBit_or, testBit_planesN M j e y he hy, Nat.testBit_shiftLeft, Nat.testBit_or,
      Nat.testBit_shiftLeft, plane_eq, plane_eq, testBit_planeN, testBit_planeN]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rcases Nat.lt_trichotomy j M with h | rfl | h
    · constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
        · exact ⟨by omega, h2⟩
        · omega
      · rintro ⟨-, h2⟩
        exact Or.inl ⟨h, h2⟩
    · have hc : 1458 * j + 729 * e + y - 1458 * j = 729 * e + y := by omega
      rw [hc]
      rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
      · have h0 : 729 * 0 + y = y := by omega
        rw [h0]
        constructor
        · rintro (⟨h1, -⟩ | ⟨-, ⟨-, h2⟩ | ⟨h1, -⟩⟩)
          · omega
          · exact ⟨by omega, h2⟩
          · omega
        · rintro ⟨-, h2⟩
          exact Or.inr ⟨by omega, Or.inl ⟨hy, h2⟩⟩
      · have h1 : 729 * 1 + y - 729 = y := by omega
        rw [h1]
        constructor
        · rintro (⟨h1, -⟩ | ⟨-, ⟨h1, -⟩ | ⟨-, -, h2⟩⟩)
          · omega
          · omega
          · exact ⟨by omega, h2⟩
        · rintro ⟨-, h2⟩
          exact Or.inr ⟨by omega, Or.inr ⟨by omega, by omega, h2⟩⟩
    · constructor
      · rintro (⟨h1, -⟩ | ⟨-, ⟨h1, -⟩ | ⟨-, h1, -⟩⟩) <;> omega
      · rintro ⟨h1, -⟩
        omega

theorem ALL_eq : ALL = 2 ^ 729 - 1 := by
  change 1 <<< 729 - 1 = 2 ^ 729 - 1
  rw [Nat.one_shiftLeft]

theorem testBit_ALL {x : Nat} (hx : x < 729) : ALL.testBit x = true := by
  rw [ALL_eq]
  exact (Nat.testBit_two_pow_sub_one 729 x).trans (decide_eq_true hx)

theorem testBit_laneP (P i y : Nat) (hy : y < 729) :
    (laneP P i).testBit y = P.testBit (729 * i + y) := by
  change ((P >>> (729 * i)) &&& ALL).testBit y = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_ALL hy, Bool.and_true]

theorem testBit_lane_planes {j e y : Nat} (hj : j < 6) (he : e < 2) (hy : y < 729) :
    (laneP planes (2 * j + e)).testBit y = decide (dg y j = e + 1) := by
  rw [testBit_laneP _ _ _ hy, planes_eq,
    show 729 * (2 * j + e) + y = 1458 * j + 729 * e + y by omega, testBit_planesN 6 j e y he hy]
  simp [hj]

theorem testBit_add3 (a1 a2 t1 t2 : Nat) {x : Nat} (hx : x < 729) :
    (add3 a1 a2 (t1, t2)).1.testBit x = ((!(t1.testBit x || t2.testBit x) && a1.testBit x) ||
      (t1.testBit x && !(a1.testBit x || a2.testBit x)) || (t2.testBit x && a2.testBit x)) ∧
    (add3 a1 a2 (t1, t2)).2.testBit x = ((!(t1.testBit x || t2.testBit x) && a2.testBit x) ||
      (t2.testBit x && !(a1.testBit x || a2.testBit x)) || (t1.testBit x && a1.testBit x)) := by
  constructor
  · change ((((ALL ^^^ (t1 ||| t2)) &&& a1) ||| (t1 &&& (ALL ^^^ (a1 ||| a2)))) |||
      (t2 &&& a2)).testBit x = _
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, testBit_ALL hx, Bool.true_xor]
  · change ((((ALL ^^^ (t1 ||| t2)) &&& a2) ||| (t2 &&& (ALL ^^^ (a1 ||| a2)))) |||
      (t1 &&& a1)).testBit x = _
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, testBit_ALL hx, Bool.true_xor]

noncomputable def zS (P f N : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (0, 0)
    (fun j ih => letN (dg f j) fun d =>
      Bool.rec (motive := fun _ => Nat × Nat)
        (add3 (laneP P (Nat.add (Nat.mul 2 j) (Nat.sub d 1)))
          (laneP P (Nat.add (Nat.mul 2 j) (Nat.sub 2 d))) ih) ih (Nat.beq d 0)) N

theorem zmask_eq (P f : Nat) : zmask P f = ALL ^^^ ((zS P f 6).1 ||| (zS P f 6).2) := by
  unfold zmask zS
  rfl

noncomputable def sdot (x f N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i s => s + dg x i * dg f i) N

theorem add3_tab : ∀ r, r < 3 → ∀ a, a < 3 → ∀ d, d < 3 → d ≠ 0 →
    ((!(decide (r = 1) || decide (r = 2)) && decide (a = d - 1 + 1)) ||
      (decide (r = 1) && !(decide (a = d - 1 + 1) || decide (a = 2 - d + 1))) ||
      (decide (r = 2) && decide (a = 2 - d + 1))) = decide ((r + a * d % 3) % 3 = 1) ∧
    ((!(decide (r = 1) || decide (r = 2)) && decide (a = 2 - d + 1)) ||
      (decide (r = 2) && !(decide (a = d - 1 + 1) || decide (a = 2 - d + 1))) ||
      (decide (r = 1) && decide (a = d - 1 + 1))) = decide ((r + a * d % 3) % 3 = 2) := by
  intro r hr a ha d hd hd0
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;>
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
  rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl <;> decide

theorem testBit_zS (f : Nat) {x : Nat} (hx : x < 729) : ∀ N, N ≤ 6 →
    (zS planes f N).1.testBit x = decide (sdot x f N % 3 = 1) ∧
    (zS planes f N).2.testBit x = decide (sdot x f N % 3 = 2)
  | 0, _ => by
    change Nat.testBit 0 x = decide (0 % 3 = 1) ∧ Nat.testBit 0 x = decide (0 % 3 = 2)
    simp
  | N + 1, hN => by
    have ih := testBit_zS f hx N (by omega)
    change (Bool.rec (motive := fun _ => Nat × Nat)
        (add3 (laneP planes (2 * N + (dg f N - 1))) (laneP planes (2 * N + (2 - dg f N)))
          (zS planes f N)) (zS planes f N) (Nat.beq (dg f N) 0)).1.testBit x =
        decide ((sdot x f N + dg x N * dg f N) % 3 = 1) ∧
      (Bool.rec (motive := fun _ => Nat × Nat)
        (add3 (laneP planes (2 * N + (dg f N - 1))) (laneP planes (2 * N + (2 - dg f N)))
          (zS planes f N)) (zS planes f N) (Nat.beq (dg f N) 0)).2.testBit x =
        decide ((sdot x f N + dg x N * dg f N) % 3 = 2)
    cases hb : Nat.beq (dg f N) 0
    · have hd0 : dg f N ≠ 0 := fun h => by
        rw [h] at hb
        cases hb
      have hd3 : dg f N < 3 := Nat.mod_lt _ (by omega)
      have l1 := testBit_lane_planes (j := N) (e := dg f N - 1) (by omega) (by omega) hx
      have l2 := testBit_lane_planes (j := N) (e := 2 - dg f N) (by omega) (by omega) hx
      generalize zS planes f N = t at ih ⊢
      obtain ⟨t1, t2⟩ := t
      obtain ⟨o1, o2⟩ := testBit_add3 (laneP planes (2 * N + (dg f N - 1)))
        (laneP planes (2 * N + (2 - dg f N))) t1 t2 hx
      change (add3 _ _ (t1, t2)).1.testBit x = _ ∧ (add3 _ _ (t1, t2)).2.testBit x = _
      rw [o1, o2, l1, l2, ih.1, ih.2, Nat.add_mod (sdot x f N)]
      have hr : sdot x f N % 3 < 3 := Nat.mod_lt _ (by omega)
      have ha : dg x N < 3 := Nat.mod_lt _ (by omega)
      exact add3_tab _ hr _ ha _ hd3 hd0
    · have hd : dg f N = 0 := Nat.eq_of_beq_eq_true hb
      change (zS planes f N).1.testBit x = _ ∧ (zS planes f N).2.testBit x = _
      rw [hd, Nat.mul_zero, Nat.add_zero]
      exact ih

theorem testBit_zmask (f : Nat) {x : Nat} (hx : x < 729) :
    (zmask planes f).testBit x = decide (dot x f = 0) := by
  obtain ⟨h1, h2⟩ := testBit_zS f hx 6 (by omega)
  rw [zmask_eq, Nat.testBit_xor, testBit_ALL hx, Nat.testBit_or, h1, h2, Bool.true_xor]
  have e : dot x f = sdot x f 6 % 3 := by
    change (dg x 0 * dg f 0 + dg x 1 * dg f 1 + (dg x 2 * dg f 2 + dg x 3 * dg f 3) +
      (dg x 4 * dg f 4 + dg x 5 * dg f 5)) % 3 = (0 + dg x 0 * dg f 0 + dg x 1 * dg f 1 +
      dg x 2 * dg f 2 + dg x 3 * dg f 3 + dg x 4 * dg f 4 + dg x 5 * dg f 5) % 3
    omega
  rw [e]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq]
  omega

def cval : List Nat → Nat → Nat
  | [], _ => 0
  | p :: C, x => (p.testBit x).toNat + 2 * cval C x

theorem bit_add_mod {r Q M : Nat} (hr : r < 2) (hM : 0 < M) :
    (r + 2 * Q) % (2 * M) = r + 2 * (Q % M) := by
  have hq := Nat.div_add_mod Q M
  have hs := Nat.mod_lt Q hM
  generalize Q / M = q at hq
  generalize Q % M = s at hq hs
  subst hq
  have e : r + 2 * (M * q + s) = (r + 2 * s) + 2 * M * q := by
    rw [Nat.mul_add, Nat.mul_assoc]
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem incC_sound : ∀ (C : List Nat) (z x : Nat),
    (incC C z).length = C.length ∧
      cval (incC C z) x = (cval C x + (z.testBit x).toNat) % 2 ^ C.length
  | [], z, x => by
    refine ⟨rfl, ?_⟩
    change 0 = (0 + _) % 1
    omega
  | p :: C, z, x => by
    obtain ⟨ih1, ih2⟩ := incC_sound C (p &&& z) x
    change ((p ^^^ z) :: incC C (p &&& z)).length = (p :: C).length ∧
      cval ((p ^^^ z) :: incC C (p &&& z)) x = _
    refine ⟨by simp [ih1], ?_⟩
    change ((p ^^^ z).testBit x).toNat + 2 * cval (incC C (p &&& z)) x =
      ((p.testBit x).toNat + 2 * cval C x + (z.testBit x).toNat) % 2 ^ (C.length + 1)
    rw [ih2, Nat.testBit_and, Nat.testBit_xor, Nat.pow_succ, Nat.mul_comm (2 ^ C.length) 2]
    have hM : 0 < 2 ^ C.length := Nat.two_pow_pos _
    generalize p.testBit x = bp
    generalize z.testBit x = bz
    have key : bp.toNat + 2 * cval C x + bz.toNat =
        (bp ^^ bz).toNat + 2 * (cval C x + (bp && bz).toNat) := by
      cases bp <;> cases bz <;> simp <;> omega
    rw [key, bit_add_mod (Bool.toNat_lt _) hM]

theorem cval_lt : ∀ (C : List Nat) (x : Nat), cval C x < 2 ^ C.length
  | [], _ => by
    change 0 < 1
    omega
  | p :: C, x => by
    have := cval_lt C x
    have := Bool.toNat_lt (p.testBit x)
    change (p.testBit x).toNat + 2 * cval C x < 2 ^ (C.length + 1)
    rw [Nat.pow_succ]
    omega

theorem countL_sound {x : Nat} (hx : x < 729) : ∀ (l : List (Nat × Nat)) (C : List Nat),
    (countL planes l C).length = C.length ∧ cval (countL planes l C) x =
      (cval C x + (l.filter fun e => dot x (e.1 % 729) == 0).length) % 2 ^ C.length
  | [], C => by
    refine ⟨rfl, ?_⟩
    change cval C x = (cval C x + 0) % 2 ^ C.length
    rw [Nat.add_zero, Nat.mod_eq_of_lt (cval_lt C x)]
  | (k, w) :: t, C => by
    obtain ⟨h1, h2⟩ := incC_sound C (zmask planes (k % 729)) x
    obtain ⟨ih1, ih2⟩ := countL_sound hx t (incC C (zmask planes (k % 729)))
    change (countL planes t (incC C (zmask planes (k % 729)))).length = C.length ∧
      cval (countL planes t (incC C (zmask planes (k % 729)))) x = _
    refine ⟨by rw [ih1, h1], ?_⟩
    rw [ih2, h1, h2, testBit_zmask _ hx, Nat.mod_add_mod, List.filter_cons]
    by_cases hd : dot x (k % 729) = 0
    · simp only [hd, decide_true, Bool.toNat_true, beq_self_eq_true, ↓reduceIte,
        List.length_cons]
      exact congrArg (· % 2 ^ C.length) (by omega)
    · simp [hd]

theorem testBit_eqE0 {x : Nat} (hx : x < 729) :
    ∀ C : List Nat, (eqE0 C).testBit x = true ↔ ∀ p ∈ C, p.testBit x = p.testBit 1
  | [] => by
    change ALL.testBit x = true ↔ _
    simp [testBit_ALL hx]
  | p :: C => by
    have e : Nat.beq ((p >>> 1) &&& 1) 1 = p.testBit 1 := by
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
      apply Bool.eq_iff_iff.mpr
      rw [Nat.beq_eq, decide_eq_true_eq]
    change ((eqE0 C) &&& selN (Nat.beq ((p >>> 1) &&& 1) 1) p (ALL ^^^ p)).testBit x = true ↔ _
    rw [e, Nat.testBit_and, Bool.and_eq_true, testBit_eqE0 hx C, List.forall_mem_cons, and_comm]
    cases hb : p.testBit 1
    · change (ALL ^^^ p).testBit x = true ∧ _ ↔ _
      rw [Nat.testBit_xor, testBit_ALL hx]
      cases p.testBit x <;> simp
    · exact Iff.rfl

theorem cval_eq_bits : ∀ (C : List Nat) (x y : Nat), cval C x = cval C y →
    ∀ p ∈ C, p.testBit x = p.testBit y
  | [], _, _, _ => fun _ h => absurd h List.not_mem_nil
  | p :: C, x, y, h => by
    change (p.testBit x).toNat + 2 * cval C x = (p.testBit y).toNat + 2 * cval C y at h
    have hx := Bool.toNat_lt (p.testBit x)
    have hy := Bool.toNat_lt (p.testBit y)
    have h1 : (p.testBit x).toNat = (p.testBit y).toNat := by omega
    have h2 : cval C x = cval C y := by omega
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · cases hbx : q.testBit x <;> cases hby : q.testBit y <;> rw [hbx, hby] at h1 <;>
        first | rfl | cases h1
    · exact cval_eq_bits C x y h2 q hq

theorem cval_count {lh lg : List (Nat × Nat)} (hlen : lh.length + lg.length < 4096) {y : Nat}
    (hy : y < 729) :
    cval (countL planes lg (countL planes lh [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) y =
      ((lh ++ lg).filter fun e => dot y (e.1 % 729) == 0).length := by
  obtain ⟨a1, a2⟩ := countL_sound hy lh [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  obtain ⟨-, b2⟩ := countL_sound hy lg (countL planes lh [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
  rw [b2, a1, a2, List.filter_append, List.length_append]
  have c0 : cval [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] y = 0 := by simp [cval]
  have l1 := List.length_filter_le (fun e : Nat × Nat => dot y (e.1 % 729) == 0) lh
  have l2 := List.length_filter_le (fun e : Nat × Nat => dot y (e.1 % 729) == 0) lg
  rw [c0]
  change ((0 + _) % 4096 + _) % 4096 = _
  rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem testBit_ALL_sub_one {x : Nat} (hx0 : 0 < x) (hx : x < 729) :
    (ALL - 1).testBit x = true := by
  have e : ALL - 1 = (2 ^ 728 - 1) <<< 1 := by
    change 1 <<< (728 + 1) - 1 - 1 = _
    rw [Nat.shiftLeft_succ, Nat.one_shiftLeft, Nat.shiftLeft_eq]
    have := Nat.two_pow_pos 728
    omega
  rw [e, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one 728 (x - 1)]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem k3OK_sound {fx : Bool} {gens : List Nat} {gk : Nat} {lh lg : List (Nat × Nat)}
    {ow : List (Nat × (Nat × Nat))} (hg : ∀ g ∈ gens, validH fx g = true)
    (h : k3OK gens gk lh lg ow = true) {x : Nat} (hx0 : 0 < x) (hx : x < 729)
    (hcnt : ((lh ++ lg).filter fun e => dot x (e.1 % 729) == 0).length =
      ((lh ++ lg).filter fun e => dot 1 (e.1 % 729) == 0).length) :
    ∃ w : List Nat, (∀ g ∈ w, g < Nat.succ (lenN gens)) ∧
      (applyW gens [gk] w 1 = x ∨ applyW gens [gk] w 1 = negV x) := by
  change andB (Nat.blt (lenN lh + lenN lg) 4096)
    (Nat.beq ((eqE0 (countL planes lg (countL planes lh [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) &&&
      (ALL - 1)) &&& (ALL ^^^ reachM gens [gk] (Nat.succ (lenN gens)) ow)) 0) = true at h
  obtain ⟨h1, h2⟩ := andB_eq_true.mp h
  have hlen := blt_true h1
  rw [lenN_eq, lenN_eq] at hlen
  have hz := Nat.eq_of_beq_eq_true h2
  have hEx : (eqE0 (countL planes lg (countL planes lh [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))).testBit
      x = true := by
    refine (testBit_eqE0 hx _).mpr (cval_eq_bits _ x 1 ?_)
    rw [cval_count hlen hx, cval_count hlen (by omega)]
    exact hcnt
  have hbit := congrArg (fun n => n.testBit x) hz
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, hEx, testBit_ALL_sub_one hx0 hx,
    testBit_ALL hx, Bool.true_and, Bool.true_xor, Bool.not_eq_false'] at hbit
  exact reachM_sound (applyL_negV hg) ow x hbit

end CFSG.KC.TwD5R
