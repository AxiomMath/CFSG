module

public import Certificates.Data.Kernel.Child3
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Arr
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Child3Reps

public section

namespace CFSG.KC.Child3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.EvenSmallLie.Child3

@[expose] def rootBody (r : Nat) (s : Array Nat × Array Nat) :
    Id (ForInStep (Array Nat × Array Nat)) :=
  pure (ForInStep.yield (s.1.set! r 0, s.2.push r))

@[expose] def innerBody (n : Nat) (S : Array (Array Nat)) (x l : Nat)
    (s : Array Nat × Array Nat × Array Nat × Array Nat) :
    Id (ForInStep (Array Nat × Array Nat × Array Nat × Array Nat)) :=
  if (decide ((S[l]!)[x]! < n) && s.2.2.1[(S[l]!)[x]!]! == n + 1) = true then
    pure (ForInStep.yield (s.1.set! (S[l]!)[x]! x, s.2.1.set! (S[l]!)[x]! l,
      s.2.2.1.set! (S[l]!)[x]! (s.2.2.1[x]! + 1), s.2.2.2.push (S[l]!)[x]!))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def outerBody (n : Nat) (S : Array (Array Nat)) (_t : Nat)
    (s : Array Nat × Array Nat × Array Nat × Array Nat × Nat) :
    Id (ForInStep (Array Nat × Array Nat × Array Nat × Array Nat × Nat)) :=
  if s.2.2.2.2 < s.2.2.2.1.size then
    (fun s1 : Array Nat × Array Nat × Array Nat × Array Nat =>
      pure (ForInStep.yield (s1.1, s1.2.1, s1.2.2.1, s1.2.2.2, s.2.2.2.2 + 1)))
      (Id.run (forIn (List.range' 0 S.size) (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
        (innerBody n S s.2.2.2.1[s.2.2.2.2]!)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

@[expose] def rootRes (n : Nat) (roots : List Nat) : Array Nat × Array Nat :=
  Id.run (forIn roots (Array.replicate n (n + 1), (#[] : Array Nat)) rootBody)

@[expose] def mainRes (n : Nat) (S : Array (Array Nat)) (roots : List Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat × Nat :=
  Id.run (forIn (List.range' 0 n) (Array.replicate n 0, Array.replicate n 0, (rootRes n roots).1,
    (rootRes n roots).2, 0) (outerBody n S))

theorem bfsForest_eq (n : Nat) (S : Array (Array Nat)) (roots : List Nat) :
    bfsForest n S roots =
      ((mainRes n S roots).1, (mainRes n S roots).2.1, (mainRes n S roots).2.2.1) := by
  unfold bfsForest mainRes rootRes
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem set!_get {a : Array Nat} {i y v : Nat} (hy : y < a.size) :
    (a.set! i v)[y]! = if i = y then v else a[y]! := by
  rw [getElem!_pos _ y (by simpa using hy), getElem!_pos a y hy]
  simp only [Array.set!]
  exact Array.getElem_setIfInBounds hy

theorem push_get {a : Array Nat} {x i : Nat} :
    (a.push x)[i]! = if i < a.size then a[i]! else if i = a.size then x else 0 := by
  by_cases h : i < a.size
  · rw [ite_eq_left h, getElem!_pos _ i (by simp; omega), getElem!_pos a i h, Array.getElem_push_lt h]
  · rw [ite_eq_right h]
    by_cases h' : i = a.size
    · subst h'
      rw [ite_eq_left rfl, getElem!_pos _ _ (by simp), Array.getElem_push_eq]
    · rw [ite_eq_right h', getElem!_neg _ _ (by simp; omega)]
      rfl

theorem length_le_of_nodup {n : Nat} {l : List Nat} (hnd : l.Nodup) (hl : ∀ y ∈ l, y < n) :
    l.length ≤ n := by
  classical
  have hs : l.toFinset ⊆ Finset.range n := fun y hy => by
    rw [List.mem_toFinset] at hy
    exact Finset.mem_range.2 (hl y hy)
  have := Finset.card_le_card hs
  rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at this

theorem mem_toList_get {a : Array Nat} {i : Nat} (hi : i < a.size) : a[i]! ∈ a.toList := by
  rw [getElem!_pos a i hi]
  exact Array.getElem_mem_toList hi

theorem forIn_list_yield {α β : Type} (f : α → β → Id (ForInStep β)) (P : List α → β → Prop)
    (h : ∀ pre a b, P pre b → ∃ b', f a b = pure (ForInStep.yield b') ∧ P (pre ++ [a]) b') :
    ∀ (l pre : List α) (init : β), P pre init → P (pre ++ l) (Id.run (forIn l init f))
  | [], pre, init, h0 => by simpa using h0
  | a :: l, pre, init, h0 => by
    obtain ⟨b', hb, hP⟩ := h pre a init h0
    have := forIn_list_yield f P h l (pre ++ [a]) b' hP
    rw [List.forIn_cons, hb]
    simpa using this

theorem roots_spec (n : Nat) (roots : List Nat) :
    (rootRes n roots).1.size = n ∧ (rootRes n roots).2.toList = roots ∧
      ∀ y < n, (rootRes n roots).1[y]! = if y ∈ roots then 0 else n + 1 := by
  unfold rootRes
  have := forIn_list_yield rootBody (fun pre (s : Array Nat × Array Nat) => s.1.size = n ∧
      s.2.toList = pre ∧ ∀ y < n, s.1[y]! = if y ∈ pre then 0 else n + 1)
    (fun pre a b ⟨h1, h2, h3⟩ => ⟨(b.1.set! a 0, b.2.push a), rfl, by simp [h1], by simp [h2],
      fun y hy => by
      rw [set!_get (by rw [h1]; exact hy), h3 y hy]
      by_cases e : a = y
      · subst e
        simp
      · simp [e, Ne.symm e]⟩) roots [] (Array.replicate n (n + 1), (#[] : Array Nat))
      ⟨by simp, rfl, fun y hy => by
        rw [getElem!_pos _ y (by simpa using hy)]
        simp⟩
  simpa using this

structure IInv (n : Nat) (S : Array (Array Nat)) (roots : List Nat) (q0 : Array Nat) (h l' : Nat)
    (par lab dep queue : Array Nat) : Prop where
  par_size : par.size = n
  lab_size : lab.size = n
  dep_size : dep.size = n
  q_lt : ∀ y ∈ queue.toList, y < n
  q_nd : queue.toList.Nodup
  pre_size : q0.size ≤ queue.size
  pre_get : ∀ i < q0.size, queue[i]! = q0[i]!
  h_lt : h < q0.size
  seen : ∀ y < n, (dep[y]! ≠ n + 1 ↔ y ∈ queue.toList)
  dep_le : ∀ i < queue.size, dep[queue[i]!]! ≤ i
  root_dep : ∀ r ∈ roots, dep[r]! = 0
  root_mem : ∀ r ∈ roots, r ∈ queue.toList
  tree : ∀ y ∈ queue.toList, y ∉ roots → par[y]! ∈ queue.toList ∧ lab[y]! < S.size ∧
    dep[par[y]!]! < dep[y]! ∧ (S[lab[y]!]!)[par[y]!]! = y
  closed : ∀ i < h, ∀ l < S.size, (S[l]!)[queue[i]!]! ∈ queue.toList
  closed_h : ∀ l < l', (S[l]!)[queue[h]!]! ∈ queue.toList

structure MInv (n : Nat) (S : Array (Array Nat)) (roots : List Nat) (t : Nat)
    (par lab dep queue : Array Nat) (h : Nat) : Prop where
  par_size : par.size = n
  lab_size : lab.size = n
  dep_size : dep.size = n
  q_lt : ∀ y ∈ queue.toList, y < n
  q_nd : queue.toList.Nodup
  h_le : h ≤ queue.size
  h_eq : h = t ∨ h = queue.size
  seen : ∀ y < n, (dep[y]! ≠ n + 1 ↔ y ∈ queue.toList)
  dep_le : ∀ i < queue.size, dep[queue[i]!]! ≤ i
  root_dep : ∀ r ∈ roots, dep[r]! = 0
  root_mem : ∀ r ∈ roots, r ∈ queue.toList
  tree : ∀ y ∈ queue.toList, y ∉ roots → par[y]! ∈ queue.toList ∧ lab[y]! < S.size ∧
    dep[par[y]!]! < dep[y]! ∧ (S[lab[y]!]!)[par[y]!]! = y
  closed : ∀ i < h, ∀ l < S.size, (S[l]!)[queue[i]!]! ∈ queue.toList

section Search

variable {n : Nat} {S : Array (Array Nat)} {roots : List Nat}

theorem inner_step (hS : ∀ l < S.size, ∀ x < n, (S[l]!)[x]! < n) {q0 : Array Nat} {h l : Nat}
    (hl : l < S.size) {s : Array Nat × Array Nat × Array Nat × Array Nat}
    (I : IInv n S roots q0 h l s.1 s.2.1 s.2.2.1 s.2.2.2) :
    ∃ s', innerBody n S q0[h]! l s = pure (ForInStep.yield s') ∧
      IInv n S roots q0 h (l + 1) s'.1 s'.2.1 s'.2.2.1 s'.2.2.2 := by
  obtain ⟨par, lab, dep, queue⟩ := s
  dsimp only at I
  have hq0 : h < queue.size := Nat.lt_of_lt_of_le I.h_lt I.pre_size
  have hx : queue[h]! = q0[h]! := I.pre_get h I.h_lt
  have hxm : q0[h]! ∈ queue.toList := hx ▸ mem_toList_get hq0
  have hxn : q0[h]! < n := I.q_lt _ hxm
  have hsz : queue.size ≤ n := by
    have := length_le_of_nodup I.q_nd I.q_lt
    simpa using this
  have hdx : dep[q0[h]!]! ≤ h := hx ▸ I.dep_le h hq0
  set x := q0[h]! with hxdef
  set y := (S[l]!)[x]! with hydef
  have hyn : y < n := hS l hl x hxn
  by_cases hc : (decide (y < n) && dep[y]! == n + 1) = true
  · have hdy : dep[y]! = n + 1 := by simpa [hyn] using hc
    have hyq : y ∉ queue.toList := fun hm => (I.seen y hyn).2 hm hdy
    have hxy : x ≠ y := fun e => hyq (e ▸ hxm)
    refine ⟨(par.set! y x, lab.set! y l, dep.set! y (dep[x]! + 1), queue.push y), ?_, ?_⟩
    · unfold innerBody
      rw [ite_eq_left hc]
    · have dget : ∀ z < n, (dep.set! y (dep[x]! + 1))[z]! = if y = z then dep[x]! + 1 else dep[z]! :=
        fun z hz => set!_get (by rw [I.dep_size]; exact hz)
      have pget : ∀ z < n, (par.set! y x)[z]! = if y = z then x else par[z]! :=
        fun z hz => set!_get (by rw [I.par_size]; exact hz)
      have lget' : ∀ z < n, (lab.set! y l)[z]! = if y = z then l else lab[z]! :=
        fun z hz => set!_get (by rw [I.lab_size]; exact hz)
      have qmem : ∀ z, z ∈ (queue.push y).toList ↔ z ∈ queue.toList ∨ z = y := by
        intro z
        simp
      have qget : ∀ i < queue.size, (queue.push y)[i]! = queue[i]! := fun i hi => by
        rw [push_get, ite_eq_left hi]
      have qne : ∀ z ∈ queue.toList, y ≠ z := fun z hz e => hyq (e ▸ hz)
      dsimp only
      refine ⟨by simp [I.par_size], by simp [I.lab_size], by simp [I.dep_size], fun z hz => ?_,
        ?_, by have := I.pre_size; simp; omega,
        fun i hi => by rw [qget i (Nat.lt_of_lt_of_le hi I.pre_size), I.pre_get i hi], I.h_lt,
        fun z hz => ?_, fun i hi => ?_, fun r hr => ?_, fun r hr => ?_, fun z hz hzr => ?_,
        fun i hi l' hl' => ?_, fun l' hl' => ?_⟩
      · rcases (qmem z).1 hz with hz | rfl
        · exact I.q_lt z hz
        · exact hyn
      · rw [Array.toList_push, List.nodup_append]
        exact ⟨I.q_nd, List.nodup_singleton y, fun a ha b hb e => by
          simp at hb
          subst hb
          exact hyq (e ▸ ha)⟩
      · rw [dget z hz, qmem]
        by_cases e : y = z
        · subst e
          simp only [↓reduceIte, or_true, iff_true]
          omega
        · rw [ite_eq_right e, I.seen z hz]
          constructor
          · exact Or.inl
          · rintro (h1 | h1)
            · exact h1
            · exact absurd h1.symm e
      · simp only [Array.size_push] at hi
        rcases Nat.lt_or_ge i queue.size with h1 | h1
        · rw [qget i h1, dget _ (I.q_lt _ (mem_toList_get h1)),
            ite_eq_right (qne _ (mem_toList_get h1))]
          exact I.dep_le i h1
        · have : i = queue.size := by omega
          subst this
          rw [push_get, ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl, dget y hyn, ite_eq_left rfl]
          omega
      · rw [dget r (I.q_lt r (I.root_mem r hr)), ite_eq_right (qne r (I.root_mem r hr))]
        exact I.root_dep r hr
      · exact (qmem r).2 (Or.inl (I.root_mem r hr))
      · have hzn : z < n := by
          rcases (qmem z).1 hz with hz | rfl
          · exact I.q_lt z hz
          · exact hyn
        rw [pget z hzn, lget' z hzn, dget z hzn]
        rcases (qmem z).1 hz with hz' | rfl
        · obtain ⟨a, b, c, d⟩ := I.tree z hz' hzr
          rw [ite_eq_right (qne z hz'), ite_eq_right (qne z hz'), ite_eq_right (qne z hz'),
            dget _ (I.q_lt _ a), ite_eq_right (qne _ a)]
          exact ⟨(qmem _).2 (Or.inl a), b, c, d⟩
        · simp only [↓reduceIte]
          rw [dget x hxn, ite_eq_right (Ne.symm hxy)]
          exact ⟨(qmem _).2 (Or.inl hxm), hl, by omega, rfl⟩
      · rw [qget i (by omega)]
        exact (qmem _).2 (Or.inl (I.closed i hi l' hl'))
      · rw [qget h hq0, hx]
        rcases Nat.lt_or_ge l' l with h1 | h1
        · have := I.closed_h l' h1
          rw [hx] at this
          exact (qmem _).2 (Or.inl this)
        · have : l' = l := by omega
          subst this
          exact (qmem _).2 (Or.inr rfl)
  · refine ⟨(par, lab, dep, queue), ?_, ?_⟩
    · unfold innerBody
      rw [ite_eq_right hc]
    · refine ⟨I.par_size, I.lab_size, I.dep_size, I.q_lt, I.q_nd, I.pre_size, I.pre_get, I.h_lt,
        I.seen, I.dep_le, I.root_dep, I.root_mem, I.tree, I.closed, fun l' hl' => ?_⟩
      rcases Nat.lt_or_ge l' l with h1 | h1
      · exact I.closed_h l' h1
      · have : l' = l := by omega
        subst this
        rw [hx]
        have hd : dep[y]! ≠ n + 1 := fun e => hc (by simp [hyn, e])
        exact (I.seen y hyn).1 hd

theorem outer_step (hS : ∀ l < S.size, ∀ x < n, (S[l]!)[x]! < n) {t : Nat}
    {s : Array Nat × Array Nat × Array Nat × Array Nat × Nat}
    (I : MInv n S roots t s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2) :
    ∃ s', outerBody n S t s = pure (ForInStep.yield s') ∧
      MInv n S roots (t + 1) s'.1 s'.2.1 s'.2.2.1 s'.2.2.2.1 s'.2.2.2.2 := by
  obtain ⟨par, lab, dep, queue, h⟩ := s
  dsimp only at I
  by_cases hh : h < queue.size
  · have hI : IInv n S roots queue h 0 par lab dep queue :=
      ⟨I.par_size, I.lab_size, I.dep_size, I.q_lt, I.q_nd, le_rfl, fun _ _ => rfl, hh, I.seen,
        I.dep_le, I.root_dep, I.root_mem, I.tree, I.closed, fun l hl => absurd hl (Nat.not_lt_zero l)⟩
    have hF := CFSG.KS.KeyBfs.forIn_range'_yield S.size 0 (par, lab, dep, queue)
      (innerBody n S queue[h]!)
      (fun l s1 => IInv n S roots queue h l s1.1 s1.2.1 s1.2.2.1 s1.2.2.2)
      (fun l hl s1 hs1 => by
        rw [Nat.zero_add]
        exact inner_step hS hl hs1) hI
    obtain ⟨s1, hs1⟩ : ∃ s1, s1 = Id.run (forIn (List.range' 0 S.size) (par, lab, dep, queue)
        (innerBody n S queue[h]!)) := ⟨_, rfl⟩
    rw [← hs1] at hF
    have ht : h = t := I.h_eq.resolve_right (Nat.ne_of_lt hh)
    refine ⟨(s1.1, s1.2.1, s1.2.2.1, s1.2.2.2, h + 1), ?_, ?_⟩
    · unfold outerBody
      rw [ite_eq_left hh]
      dsimp only
      rw [← hs1]
    · dsimp only
      refine ⟨hF.par_size, hF.lab_size, hF.dep_size, hF.q_lt, hF.q_nd,
        Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hh hF.pre_size), Or.inl (by omega), hF.seen,
        hF.dep_le, hF.root_dep, hF.root_mem, hF.tree, fun i hi l hl => ?_⟩
      rcases Nat.lt_or_ge i h with h1 | h1
      · exact hF.closed i h1 l hl
      · have : i = h := by omega
        subst this
        exact hF.closed_h l hl
  · refine ⟨(par, lab, dep, queue, h), ?_, ?_⟩
    · unfold outerBody
      rw [ite_eq_right hh]
    · dsimp only
      exact ⟨I.par_size, I.lab_size, I.dep_size, I.q_lt, I.q_nd, I.h_le,
        Or.inr (by have := I.h_le; omega), I.seen, I.dep_le, I.root_dep, I.root_mem, I.tree,
        I.closed⟩

theorem main_spec (hS : ∀ l < S.size, ∀ x < n, (S[l]!)[x]! < n) (hroots : ∀ r ∈ roots, r < n)
    (hnd : roots.Nodup) :
    MInv n S roots n (mainRes n S roots).1 (mainRes n S roots).2.1 (mainRes n S roots).2.2.1
      (mainRes n S roots).2.2.2.1 (mainRes n S roots).2.2.2.2 := by
  obtain ⟨r1, r2, r3⟩ := roots_spec n roots
  have h0 : MInv n S roots 0 (Array.replicate n 0) (Array.replicate n 0) (rootRes n roots).1
      (rootRes n roots).2 0 := by
    refine ⟨by simp, by simp, r1, fun y hy => hroots y (by rw [r2] at hy; exact hy),
      by rw [r2]; exact hnd, Nat.zero_le _, Or.inl rfl, fun y hy => ?_, fun i hi => ?_,
      fun r hr => ?_, fun r hr => by rw [r2]; exact hr,
      fun y hy hyr => absurd (by rw [r2] at hy; exact hy) hyr,
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    · rw [r3 y hy, r2]
      by_cases hm : y ∈ roots
      · simp [hm]
      · simp [hm]
    · have hm : (rootRes n roots).2[i]! ∈ roots := by
        have := mem_toList_get hi
        rwa [r2] at this
      rw [r3 _ (hroots _ hm), ite_eq_left hm]
      exact Nat.zero_le _
    · rw [r3 r (hroots r hr), ite_eq_left hr]
  unfold mainRes
  exact CFSG.KS.KeyBfs.forIn_range'_yield n 0 _ (outerBody n S)
    (fun t s => MInv n S roots t s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2)
    (fun t _ s hs => by
      rw [Nat.zero_add]
      exact outer_step hS hs) h0

theorem forestOK_bfs (hS : ∀ l < S.size, ∀ x < n, (S[l]!)[x]! < n) (hroots : ∀ r ∈ roots, r < n)
    (hnd : roots.Nodup)
    (hreach : ∀ Q : List Nat, (∀ r ∈ roots, r ∈ Q) → (∀ x ∈ Q, ∀ l < S.size, (S[l]!)[x]! ∈ Q) →
      ∀ p < n, p ∈ Q) :
    forestOK n S roots (bfsForest n S roots).1 (bfsForest n S roots).2.1
      (bfsForest n S roots).2.2 = true := by
  have M := main_spec hS hroots hnd
  rw [bfsForest_eq]
  generalize mainRes n S roots = s at M ⊢
  obtain ⟨par, lab, dep, queue, h⟩ := s
  dsimp only at M ⊢
  have hhq : h = queue.size := by
    rcases M.h_eq with e | e
    · have := length_le_of_nodup M.q_nd M.q_lt
      simp only [Array.length_toList] at this
      have := M.h_le
      omega
    · exact e
  have hall := hreach queue.toList M.root_mem (fun x hx l hl => by
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hx
    have hi' : i < queue.size := by simpa using hi
    have hq : queue[i]! = x := by
      rw [getElem!_pos _ i hi']
      simpa using e
    rw [← hq]
    exact M.closed i (hhq ▸ hi') l hl)
  unfold forestOK
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro p hp
  have hpq := hall p hp
  by_cases hr : p ∈ roots
  · have hc : roots.contains p = true := by simpa using hr
    rw [M.root_dep p hr, hc]
    rfl
  · obtain ⟨a, b, c, d⟩ := M.tree p hpq hr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact Or.inr ⟨⟨⟨M.q_lt _ a, b⟩, c⟩, d⟩

end Search

theorem reach_of_forestK {n w kS : Nat} {PS FP FL FD : Nat → Nat} {S : Array (Array Nat)}
    {roots : List Nat} (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hf : forestK n w PS kS roots FP FL FD = true) (Q : List Nat) (hr : ∀ r ∈ roots, r ∈ Q)
    (hc : ∀ x ∈ Q, ∀ l < S.size, (S[l]!)[x]! ∈ Q) : ∀ p < n, p ∈ Q := by
  have key : ∀ d, ∀ p < n, FD p = d → p ∈ Q := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro p hp hd
      have hk := allN_spec hf p hp
      cases e : Bool.rec (motive := fun _ => Bool) false (roots.contains p) (Nat.beq (FD p) 0)
      · rw [e] at hk
        simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at hk
        obtain ⟨h1, h2, h3, h4⟩ := hk
        have hm := ih _ (hd ▸ h3) (FP p) h1 rfl
        have := hc _ hm (FL p) (by rw [hS.1]; exact h2)
        rwa [hS.2 _ h2, unpack_get' h1, h4] at this
      · rw [bAnd_iff] at e
        exact hr p (by simpa using e.2)
  exact fun p hp => key _ p hp rfl

theorem centOK_of {n w kS : Nat} {PS PSI FP FL FD : Nat → Nat} {S : Array (Array Nat)}
    {rs : List (Nat × List (List Int))} (hsz : szOK n w = true) (hnd : (rs.map Prod.fst).Nodup)
    (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hst : rs.all (fun r => stabK n w PS PSI kS r.1 r.2) = true)
    (hf : forestK n w PS kS (rs.map Prod.fst) FP FL FD = true) :
    centOK n S rs = true := by
  have hSlt : ∀ l < S.size, ∀ x < n, (S[l]!)[x]! < n := by
    intro l hl x hx
    rw [hS.1] at hl
    rw [hS.2 l hl, unpack_get' hx]
    exact Nat.blt_eq.mp (allN_spec (range_of_permOK (allN_spec hp l hl)) x hx)
  have hstab : ∀ r ∈ rs, stabK n w PS PSI kS r.1 r.2 = true := List.all_eq_true.1 hst
  have hroots : ∀ r ∈ rs.map Prod.fst, r < n := by
    intro r hr
    obtain ⟨⟨r, ws⟩, hm, rfl⟩ := List.mem_map.1 hr
    have := hstab _ hm
    unfold stabK at this
    exact Nat.blt_eq.mp ((bAnd_iff _ _).1 this).1
  unfold centOK
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun r hr => ?_, forestOK_bfs hSlt hroots hnd (reach_of_forestK hS hf)⟩
  obtain ⟨r, ws⟩ := r
  have hk := hstab _ hr
  unfold stabK at hk
  simp only [bAnd_iff, Nat.blt_eq, List.all_eq_true] at hk
  obtain ⟨h1, h2, h3, h4⟩ := hk
  have hw : ∀ wd ∈ ws, wordA n S (rawInvs n S) wd = unpack n w (wv n w PS PSI wd) := by
    intro wd hwd
    have hwe : wordEqK n w (mask w) (pidn n w) PS PSI kS wd (wv n w PS PSI wd) = true := by
      unfold wordEqK
      rw [hsz, h2 wd hwd]
      exact Nat.beq_refl _
    exact (wordEqK_sound hS hp hwe).1
  have hv : ∀ wd ∈ ws, ∀ q < n, (wordA n S (rawInvs n S) wd)[q]! = pg w (mask w) (wv n w PS PSI wd) q :=
    fun wd hwd q hq => by rw [hw wd hwd, unpack_get' hq]
  unfold stabOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.all_map,
    Function.comp_apply]
  refine ⟨⟨⟨h1, fun wd hwd => ?_⟩, fun wd hwd => ?_⟩, ?_⟩
  · rw [hS.1]
    exact lettersK_sound (h2 wd hwd)
  · rw [hv wd hwd r h1, beq_iff_eq]
    exact Nat.eq_of_beq_eq_true (h3 wd hwd)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro q hq
    have hk := allN_spec h4 q hq
    cases e : Nat.beq q r
    · rw [e] at hk
      have hne : q ≠ r := fun h => by rw [h, Nat.beq_refl] at e; exact Bool.noConfusion e
      obtain ⟨wd, hwd, hm⟩ := List.any_eq_true.1 hk
      rw [Bool.or_eq_true, List.any_map]
      refine Or.inr (List.any_eq_true.2 ⟨wd, hwd, ?_⟩)
      simp only [Function.comp_apply]
      rw [hv wd hwd q hq]
      cases e2 : Nat.beq (pg w (mask w) (wv n w PS PSI wd) q) q
      · have : pg w (mask w) (wv n w PS PSI wd) q ≠ q := fun h => by
          rw [h, Nat.beq_refl] at e2
          exact Bool.noConfusion e2
        simpa using this
      · rw [e2] at hm
        exact absurd hm Bool.false_ne_true
    · have : q = r := Nat.eq_of_beq_eq_true e
      simp [this]

end CFSG.KC.Child3

end
