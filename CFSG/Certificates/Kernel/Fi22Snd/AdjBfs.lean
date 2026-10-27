module

public import Certificates.Data.CFSGNative.Schreier.Refine

public section

namespace CFSG.KC.Fi22Snd

open CFSG.Certificates.Native

private abbrev AdjIn := Array (List Nat) × Array Bool × Array Nat

private abbrev AdjSt := Array (List Nat) × Array Bool × Array Nat × Nat

private def adjInner (gens : Array (Array Nat)) (x k : Nat) (s : AdjIn) : Id (ForInStep AdjIn) :=
  if (!s.2.1[(gens[k]!)[x]!]!) = true then
    pure (ForInStep.yield (s.1.set! (gens[k]!)[x]! (imgSorted gens[k]! s.1[x]!),
      s.2.1.set! (gens[k]!)[x]! true, s.2.2.push (gens[k]!)[x]!))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2))

private def adjOuter (gens : Array (Array Nat)) (_ : Nat) (s : AdjSt) : Id (ForInStep AdjSt) :=
  if s.2.2.2 < s.2.2.1.size then
    (fun r : AdjIn => pure (ForInStep.yield (r.1, r.2.1, r.2.2, s.2.2.2 + 1)))
      (Id.run (forIn (List.range' 0 gens.size) (s.1, s.2.1, s.2.2.1)
        (adjInner gens s.2.2.1[s.2.2.2]!)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

private def adjInit (n : Nat) (root : List Nat) : AdjSt :=
  ((Array.replicate n []).set! 0 root, (Array.replicate n false).set! 0 true, #[0], 0)

private theorem adjSearch_eq_loop (n : Nat) (gens : Array (Array Nat)) (root : List Nat) :
    adjSearch n gens root =
      (Id.run (forIn (List.range' 0 n) (adjInit n root) (adjOuter gens))).1 := by
  unfold adjSearch adjInit
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private theorem adjForIn_yield {β : Type} (n s : Nat) (init : β) (f : Nat → β → Id (ForInStep β))
    (P : Nat → β → Prop)
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

private theorem set!_get {α : Type} [Inhabited α] {a : Array α} {y z : Nat} {v : α}
    (hy : y < a.size) : (a.set! y v)[z]! = if y = z then v else a[z]! := by
  by_cases h : y = z
  · subst h
    rw [if_pos rfl]
    exact Array.getElem!_set!_self a y v hy
  · rw [if_neg h]
    exact Array.getElem!_set!_ne a y z v h

private theorem push_get_lt {a : Array Nat} {y i : Nat} (h : i < a.size) :
    (a.push y)[i]! = a[i]! := by
  rw [getElem!_pos (a.push y) i (by simp; omega), Array.getElem_push_lt h, getElem!_pos a i h]

private theorem push_get_eq {a : Array Nat} {y : Nat} : (a.push y)[a.size]! = y := by
  rw [getElem!_pos (a.push y) a.size (by simp), Array.getElem_push_eq]

private structure Core (n : Nat) (Row : Nat → List Nat) (nbr : Array (List Nat))
    (seen : Array Bool) (queue : Array Nat) : Prop where
  nbr_size : nbr.size = n
  seen_size : seen.size = n
  nbr_row : ∀ y < n, seen[y]! = true → nbr[y]! = Row y
  q_lt : ∀ z ∈ queue, z < n
  q_nodup : queue.toList.Nodup
  q_mem : ∀ z < n, seen[z]! = true ↔ z ∈ queue
  seen_zero : seen[0]! = true

private structure InnerInv (n : Nat) (gens : Array (Array Nat)) (Row : Nat → List Nat) (x : Nat)
    (seen0 : Array Bool) (queue0 : Array Nat) (k : Nat) (nbr : Array (List Nat))
    (seen : Array Bool) (queue : Array Nat) : Prop where
  core : Core n Row nbr seen queue
  mono : ∀ z : Nat, seen0[z]! = true → seen[z]! = true
  pre_size : queue0.size ≤ queue.size
  pre_get : ∀ i < queue0.size, queue[i]! = queue0[i]!
  done : ∀ l < k, seen[(gens[l]!)[x]!]! = true

private structure Inv (n : Nat) (gens : Array (Array Nat)) (Row : Nat → List Nat) (j : Nat)
    (nbr : Array (List Nat)) (seen : Array Bool) (queue : Array Nat) (head : Nat) : Prop where
  core : Core n Row nbr seen queue
  head_le : head ≤ queue.size
  proc : ∀ i < head, ∀ k < gens.size, seen[(gens[k]!)[queue[i]!]!]! = true
  term : head = queue.size ∨ j ≤ head

private theorem adjInner_step {n : Nat} {gens : Array (Array Nat)} {Row : Nat → List Nat}
    (hlt : ∀ k < gens.size, ∀ x < n, (gens[k]!)[x]! < n)
    (himg : ∀ k < gens.size, ∀ x < n, imgSorted gens[k]! (Row x) = Row (gens[k]!)[x]!)
    {x : Nat} (hx : x < n) {seen0 : Array Bool} {queue0 : Array Nat} (hx0 : seen0[x]! = true)
    {k : Nat} (hk : k < gens.size) {s : AdjIn}
    (I : InnerInv n gens Row x seen0 queue0 k s.1 s.2.1 s.2.2) :
    ∃ s', adjInner gens x k s = pure (ForInStep.yield s') ∧
      InnerInv n gens Row x seen0 queue0 (k + 1) s'.1 s'.2.1 s'.2.2 := by
  obtain ⟨nbr, seen, queue⟩ := s
  dsimp only at I
  have hy : (gens[k]!)[x]! < n := hlt k hk x hx
  by_cases hc : seen[(gens[k]!)[x]!]! = true
  · refine ⟨(nbr, seen, queue), ?_, I.core, I.mono, I.pre_size, I.pre_get, fun l hl => ?_⟩
    · simp only [adjInner, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · by_cases hlk : l < k
      · exact I.done l hlk
      · have : l = k := by omega
        subst this
        exact hc
  · have hnc : seen[(gens[k]!)[x]!]! = false := by simpa using hc
    have hxr : nbr[x]! = Row x := I.core.nbr_row x hx (I.mono x hx0)
    have hstep : adjInner gens x k (nbr, seen, queue) =
        pure (ForInStep.yield (nbr.set! (gens[k]!)[x]! (imgSorted gens[k]! nbr[x]!),
          seen.set! (gens[k]!)[x]! true, queue.push (gens[k]!)[x]!)) := by
      simp only [adjInner, hnc, Bool.not_false, ↓reduceIte]
    refine ⟨_, hstep, ?_⟩
    have himgk := himg k hk x hx
    rw [hxr] at ⊢
    generalize hyd : (gens[k]!)[x]! = y at hc hy himgk ⊢
    have hys : y < seen.size := by rw [I.core.seen_size]; exact hy
    have hyn : y < nbr.size := by rw [I.core.nbr_size]; exact hy
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · dsimp only
      rw [Array.size_set!]
      exact I.core.nbr_size
    · dsimp only
      rw [Array.size_set!]
      exact I.core.seen_size
    · intro z hz hzs
      dsimp only at hzs ⊢
      rw [set!_get hys] at hzs
      rw [set!_get hyn]
      by_cases hyz : y = z
      · subst hyz
        rw [if_pos rfl]
        exact himgk
      · rw [if_neg hyz] at hzs ⊢
        exact I.core.nbr_row z hz hzs
    · intro z hz
      dsimp only at hz
      rw [Array.mem_push] at hz
      rcases hz with hz | rfl
      · exact I.core.q_lt z hz
      · exact hy
    · dsimp only
      rw [Array.toList_push, List.nodup_append]
      refine ⟨I.core.q_nodup, by simp, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro e
      subst e
      exact hc ((I.core.q_mem a hy).2 (Array.mem_toList_iff.1 ha))
    · intro z hz
      dsimp only
      rw [set!_get hys, Array.mem_push]
      by_cases hyz : y = z
      · subst hyz
        simp
      · rw [if_neg hyz, I.core.q_mem z hz]
        simp [Ne.symm hyz]
    · dsimp only
      rw [set!_get hys]
      by_cases h0 : y = 0
      · rw [if_pos h0]
      · rw [if_neg h0]
        exact I.core.seen_zero
    · intro z hz
      dsimp only
      rw [set!_get hys]
      by_cases hyz : y = z
      · rw [if_pos hyz]
      · rw [if_neg hyz]
        exact I.mono z hz
    · dsimp only
      rw [Array.size_push]
      have := I.pre_size
      omega
    · intro i hi
      dsimp only
      rw [push_get_lt (Nat.lt_of_lt_of_le hi I.pre_size)]
      exact I.pre_get i hi
    · intro l hl
      dsimp only
      rw [set!_get hys]
      by_cases hlk : l < k
      · by_cases hyz : y = (gens[l]!)[x]!
        · rw [if_pos hyz]
        · rw [if_neg hyz]
          exact I.done l hlk
      · have : l = k := by omega
        subst this
        rw [hyd, if_pos rfl]

private theorem adjOuter_step {n : Nat} {gens : Array (Array Nat)} {Row : Nat → List Nat}
    (hlt : ∀ k < gens.size, ∀ x < n, (gens[k]!)[x]! < n)
    (himg : ∀ k < gens.size, ∀ x < n, imgSorted gens[k]! (Row x) = Row (gens[k]!)[x]!)
    {j : Nat} {s : AdjSt} (I : Inv n gens Row j s.1 s.2.1 s.2.2.1 s.2.2.2) :
    ∃ s', adjOuter gens j s = pure (ForInStep.yield s') ∧
      Inv n gens Row (j + 1) s'.1 s'.2.1 s'.2.2.1 s'.2.2.2 := by
  obtain ⟨nbr, seen, queue, head⟩ := s
  dsimp only at I
  by_cases hh : head < queue.size
  · have hxm : queue[head]! ∈ queue := by
      rw [getElem!_pos queue head hh]
      exact Array.getElem_mem hh
    have hx : queue[head]! < n := I.core.q_lt _ hxm
    have hx0 : seen[queue[head]!]! = true := (I.core.q_mem _ hx).2 hxm
    have hF := adjForIn_yield gens.size 0 (nbr, seen, queue) (adjInner gens queue[head]!)
      (fun k s1 => InnerInv n gens Row queue[head]! seen queue k s1.1 s1.2.1 s1.2.2)
      (fun k hk s1 hs1 => by
        rw [Nat.zero_add]
        exact adjInner_step hlt himg hx hx0 hk hs1)
      ⟨I.core, fun z h => h, Nat.le_refl _, fun i _ => rfl,
        fun l hl => absurd hl (Nat.not_lt_zero l)⟩
    obtain ⟨s1, hs1⟩ : ∃ s1, s1 = Id.run (forIn (List.range' 0 gens.size) (nbr, seen, queue)
        (adjInner gens queue[head]!)) := ⟨_, rfl⟩
    rw [← hs1] at hF
    refine ⟨(s1.1, s1.2.1, s1.2.2, head + 1), ?_, ?_⟩
    · unfold adjOuter
      rw [if_pos hh]
      dsimp only
      rw [← hs1]
    · dsimp only
      refine ⟨hF.core, ?_, ?_, ?_⟩
      · have := hF.pre_size
        omega
      · intro i hi k hk
        by_cases hih : i < head
        · rw [hF.pre_get i (by omega)]
          exact hF.mono _ (I.proc i hih k hk)
        · have : i = head := by omega
          subst this
          rw [hF.pre_get i hh]
          exact hF.done k hk
      · rcases I.term with h | h
        · omega
        · right
          omega
  · refine ⟨(nbr, seen, queue, head), ?_, ?_⟩
    · unfold adjOuter
      rw [if_neg hh]
    · dsimp only
      exact ⟨I.core, I.head_le, I.proc, Or.inl (by have := I.head_le; omega)⟩

private theorem adjInit_inv {n : Nat} (gens : Array (Array Nat)) (Row : Nat → List Nat)
    (hn : 0 < n) :
    Inv n gens Row 0 ((Array.replicate n []).set! 0 (Row 0)) ((Array.replicate n false).set! 0 true)
      #[0] 0 := by
  have hs : 0 < (Array.replicate n false).size := by simpa using hn
  have hnb : 0 < (Array.replicate n ([] : List Nat)).size := by simpa using hn
  have hseen : ∀ z, z < n → (((Array.replicate n false).set! 0 true)[z]! = true ↔ z = 0) := by
    intro z hz
    rw [set!_get hs]
    by_cases h : 0 = z
    · subst h
      simp
    · rw [if_neg h, getElem!_pos _ z (by simpa using hz), Array.getElem_replicate]
      simp
      omega
  refine ⟨⟨by simp, by simp, ?_, ?_, by decide, ?_, (hseen 0 hn).2 rfl⟩, Nat.zero_le _,
    fun i hi => absurd hi (Nat.not_lt_zero i), Or.inr (Nat.le_refl _)⟩
  · intro y hy hys
    have h0 := (hseen y hy).1 hys
    subst h0
    rw [set!_get hnb, if_pos rfl]
  · intro z hz
    simp at hz
    subst hz
    exact hn
  · intro z hz
    rw [hseen z hz]
    simp

theorem adjSearch_eq {n : Nat} {gens : Array (Array Nat)} {Row : Nat → List Nat} (hn : 0 < n)
    (hlt : ∀ k < gens.size, ∀ x < n, (gens[k]!)[x]! < n)
    (himg : ∀ k < gens.size, ∀ x < n, imgSorted gens[k]! (Row x) = Row (gens[k]!)[x]!)
    (hreach : ∀ P : Nat → Prop, P 0 → (∀ p < n, P p → ∀ k < gens.size, P (gens[k]!)[p]!) →
      ∀ x < n, P x) :
    adjSearch n gens (Row 0) = Array.ofFn (n := n) fun x => Row x.val := by
  rw [adjSearch_eq_loop]
  have hF := adjForIn_yield n 0 (adjInit n (Row 0)) (adjOuter gens)
    (fun j s => Inv n gens Row j s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun j _ s hs => by
      rw [Nat.zero_add]
      exact adjOuter_step hlt himg hs) (adjInit_inv gens Row hn)
  generalize Id.run (forIn (List.range' 0 n) (adjInit n (Row 0)) (adjOuter gens)) = s at hF ⊢
  obtain ⟨nbr, seen, queue, head⟩ := s
  dsimp only at hF ⊢
  have hq : queue.size ≤ n := by
    have := List.Nodup.length_le_of_subset hF.core.q_nodup (l₂ := List.range n)
      (fun z hz => List.mem_range.2 (hF.core.q_lt z (Array.mem_toList_iff.1 hz)))
    simpa using this
  have hhead : head = queue.size := by
    rcases hF.term with h | h
    · exact h
    · have := hF.head_le
      omega
  have hcl : ∀ p < n, seen[p]! = true → ∀ k < gens.size, seen[(gens[k]!)[p]!]! = true := by
    intro p hp hps k hk
    obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 ((hF.core.q_mem p hp).1 hps)
    have := hF.proc i (by omega) k hk
    rw [getElem!_pos queue i hi, e] at this
    exact this
  have hall := hreach (fun y => seen[y]! = true) hF.core.seen_zero hcl
  apply Array.ext
  · rw [Array.size_ofFn]
    exact hF.core.nbr_size
  · intro i h1 h2
    rw [Array.getElem_ofFn]
    have hi : i < n := by rw [← hF.core.nbr_size]; exact h1
    have := hF.core.nbr_row i hi (hall i hi)
    rw [getElem!_pos nbr i h1] at this
    exact this

theorem strictIncr_of_pairwise : ∀ {l : List Nat}, l.Pairwise (· < ·) → strictIncr l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    simp only [strictIncr, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, strictIncr_of_pairwise h.of_cons⟩

end CFSG.KC.Fi22Snd

end
