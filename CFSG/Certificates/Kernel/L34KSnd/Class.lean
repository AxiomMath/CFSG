
module

public import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.HeAutKLoops
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34KSnd

open CFSG.PSL3Four.Native

@[expose] def bodyA (m : Nat) (cj : Nat → Nat → Nat) (k a : Nat)
    (__s : Array (Nat × Nat) × Std.HashMap Nat Unit) :
    Id (ForInStep (Array (Nat × Nat) × Std.HashMap Nat Unit)) :=
  have cls := __s.fst
  have seen := __s.snd
  have p := cj a k
  if (decide (p < m) && !seen.contains p) = true then
    have seen := seen.insert p ()
    have cls := cls.push (p, a)
    pure (ForInStep.yield (cls, seen))
  else pure (ForInStep.yield (cls, seen))

@[expose] def bodyL (used : Array Bool) (target : Array Nat) (sz i : Nat) (__s : Nat) :
    Id (ForInStep Nat) :=
  have l := __s
  if (l == target.size && !used[i]! && target[i]! == sz) = true then
    have l := i
    pure (ForInStep.yield l)
  else pure (ForInStep.yield l)

@[expose] def bodyS (l : Nat) (x : Nat × Nat) (__s : Array Nat × Array Nat) :
    Id (ForInStep (Array Nat × Array Nat)) :=
  have lab := __s.fst
  have wit := __s.snd
  match x with
  | (p, a) =>
    have lab := lab.set! p l
    have wit := wit.set! p a
    pure (ForInStep.yield (lab, wit))

abbrev CSt := Array Nat × Array Nat × Array Nat × Array Bool

@[expose] def bodyK (m : Nat) (cj : Nat → Nat → Nat) (target : Array Nat) (k : Nat) (__s : CSt) :
    Id (ForInStep CSt) :=
  have lab := __s.fst
  have __s := __s.snd
  have wit := __s.fst
  have __s := __s.snd
  have reps := __s.fst
  have used := __s.snd
  if (lab[k]! == m) = true then
    have cls : Array (Nat × Nat) := #[]
    have seen : Std.HashMap Nat Unit := ∅
    do
    let __s ← forIn [:m] (cls, seen) (bodyA m cj k)
    have cls : Array (Nat × Nat) := __s.fst
    have l : Nat := target.size
    let __s ← forIn [:target.size] l (bodyL used target cls.size)
    have l : Nat := __s
    have __do_jp : Unit → Array Nat → Array Bool → Id (ForInStep CSt) :=
      fun (__r : Unit) (reps : Array Nat) (used : Array Bool) => do
      let __s ← forIn cls (lab, wit) (bodyS l)
      have lab : Array Nat := __s.fst
      have wit : Array Nat := __s.snd
      pure (ForInStep.yield (lab, wit, reps, used))
    if l < target.size then
      have used := used.set! l true
      have reps := reps.set! l k
      __do_jp () reps used
    else __do_jp () reps used
  else pure (ForInStep.yield (lab, wit, reps, used))

@[expose] def classLoopN (m : Nat) (cj : Nat → Nat → Nat) (target : Array Nat) : ClassData :=
  Id.run (have lab := Array.replicate m m
    have wit := Array.replicate m 0
    have reps := Array.replicate target.size 0
    have used := Array.replicate target.size false
    do
    let __s ← forIn [:m] (lab, wit, reps, used) (bodyK m cj target)
    have lab : Array Nat := __s.fst
    have __s : Array Nat × Array Nat × Array Bool := __s.snd
    have wit : Array Nat := __s.fst
    have __s : Array Nat × Array Bool := __s.snd
    have reps : Array Nat := __s.fst
    pure { lab := lab, reps := reps, wit := wit })

theorem classData_eq_loop (n : Nat) (T : Array Tab) (target : Array Nat) :
    classData n T target = classLoopN T.size
      (fun a k => posOf (indexOf T) T (conjTab n T[a]! (T.map (invTab n))[a]! T[k]!)) target :=
  rfl

theorem forIn_range_eq {β : Type} (n : Nat) (init : β) (f : Nat → β → Id (ForInStep β)) :
    forIn [:n] init f = forIn (List.range' 0 n) init f := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]

@[expose] def clsOf (m : Nat) (cj : Nat → Nat → Nat) (k : Nat) : Array (Nat × Nat) :=
  (Id.run (forIn (List.range' 0 m) ((#[] : Array (Nat × Nat)), (∅ : Std.HashMap Nat Unit))
    (bodyA m cj k))).1

@[expose] def labOf (used : Array Bool) (target : Array Nat) (sz : Nat) : Nat :=
  Id.run (forIn (List.range' 0 target.size) target.size (bodyL used target sz))

@[expose] def setOf (cls : Array (Nat × Nat)) (l : Nat) (lab wit : Array Nat) :
    Array Nat × Array Nat :=
  Id.run (forIn cls (lab, wit) (bodyS l))

theorem bodyK_eq (m : Nat) (cj : Nat → Nat → Nat) (target : Array Nat) (k : Nat) (s : CSt) :
    bodyK m cj target k s =
      if (s.1[k]! == m) = true then
        if labOf s.2.2.2 target (clsOf m cj k).size < target.size then
          pure (ForInStep.yield
            ((setOf (clsOf m cj k) (labOf s.2.2.2 target (clsOf m cj k).size) s.1 s.2.1).1,
              (setOf (clsOf m cj k) (labOf s.2.2.2 target (clsOf m cj k).size) s.1 s.2.1).2,
              s.2.2.1.set! (labOf s.2.2.2 target (clsOf m cj k).size) k,
              s.2.2.2.set! (labOf s.2.2.2 target (clsOf m cj k).size) true))
        else
          pure (ForInStep.yield
            ((setOf (clsOf m cj k) (labOf s.2.2.2 target (clsOf m cj k).size) s.1 s.2.1).1,
              (setOf (clsOf m cj k) (labOf s.2.2.2 target (clsOf m cj k).size) s.1 s.2.1).2,
              s.2.2.1, s.2.2.2))
      else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2)) := by
  unfold bodyK
  simp only [forIn_range_eq]
  rfl

theorem classLoopN_eq (m : Nat) (cj : Nat → Nat → Nat) (target : Array Nat) :
    classLoopN m cj target =
      { lab := (Id.run (forIn (List.range' 0 m) (Array.replicate m m, Array.replicate m 0,
            Array.replicate target.size 0, Array.replicate target.size false)
              (bodyK m cj target))).1
        reps := (Id.run (forIn (List.range' 0 m) (Array.replicate m m, Array.replicate m 0,
            Array.replicate target.size 0, Array.replicate target.size false)
              (bodyK m cj target))).2.2.1
        wit := (Id.run (forIn (List.range' 0 m) (Array.replicate m m, Array.replicate m 0,
            Array.replicate target.size 0, Array.replicate target.size false)
              (bodyK m cj target))).2.1 } := by
  unfold classLoopN
  simp only [forIn_range_eq]
  rfl

theorem condA {p m : Nat} {b : Bool} : (decide (p < m) && !b) = true ↔ p < m ∧ b = false := by
  cases b <;> simp

theorem condL {l N t sz : Nat} {u : Bool} :
    (l == N && !u && t == sz) = true ↔ l = N ∧ u = false ∧ t = sz := by
  cases u <;> simp

theorem bodyA_eq (m : Nat) (cj : Nat → Nat → Nat) (k a : Nat)
    (s : Array (Nat × Nat) × Std.HashMap Nat Unit) :
    bodyA m cj k a s = pure (ForInStep.yield
      (if cj a k < m ∧ s.2.contains (cj a k) = false then
        (s.1.push (cj a k, a), s.2.insert (cj a k) ()) else (s.1, s.2))) := by
  unfold bodyA
  dsimp only
  by_cases h : cj a k < m ∧ s.2.contains (cj a k) = false
  · rw [if_pos h, if_pos (condA.2 h)]
  · rw [if_neg h, if_neg (mt condA.1 h)]

theorem bodyL_eq (used : Array Bool) (target : Array Nat) (sz i l : Nat) :
    bodyL used target sz i l = pure (ForInStep.yield
      (if l = target.size ∧ used[i]! = false ∧ target[i]! = sz then i else l)) := by
  unfold bodyL
  dsimp only
  by_cases h : l = target.size ∧ used[i]! = false ∧ target[i]! = sz
  · rw [if_pos h, if_pos (condL.2 h)]
  · rw [if_neg h, if_neg (mt condL.1 h)]

theorem bodyS_eq (l : Nat) (x : Nat × Nat) (s : Array Nat × Array Nat) :
    bodyS l x s = pure (ForInStep.yield (s.1.set! x.1 l, s.2.set! x.1 x.2)) := rfl

theorem clsOf_spec (m : Nat) (cj : Nat → Nat → Nat) (k : Nat) :
    ((clsOf m cj k).toList.map Prod.fst).Nodup ∧
      (∀ x ∈ (clsOf m cj k).toList, x.1 < m ∧ x.2 < m ∧ cj x.2 k = x.1) ∧
      ∀ p, p ∈ (clsOf m cj k).toList.map Prod.fst ↔ p < m ∧ ∃ a < m, cj a k = p := by
  have key := CFSG.KS.BfsReplay.forIn_range'_yield m 0
    ((#[] : Array (Nat × Nat)), (∅ : Std.HashMap Nat Unit)) (bodyA m cj k)
    (fun j s => (s.1.toList.map Prod.fst).Nodup ∧
      (∀ x ∈ s.1.toList, x.1 < m ∧ x.2 < j ∧ cj x.2 k = x.1) ∧
      ∀ p, (p ∈ s.1.toList.map Prod.fst ↔ p < m ∧ ∃ a < j, cj a k = p) ∧
        (s.2.contains p = true ↔ p ∈ s.1.toList.map Prod.fst))
    (fun j hj s hP => ?_) ?_
  · obtain ⟨h1, h2, h3⟩ := key
    refine ⟨h1, h2, fun p => (h3 p).1⟩
  · obtain ⟨hnd, hmem, hiff⟩ := hP
    refine ⟨_, by rw [Nat.zero_add, bodyA_eq], ?_⟩
    by_cases hc : cj j k < m ∧ s.2.contains (cj j k) = false
    · rw [if_pos hc]
      obtain ⟨hlt, hns⟩ := hc
      have hnot : cj j k ∉ s.1.toList.map Prod.fst := fun h => by
        rw [← (hiff _).2] at h
        rw [h] at hns
        exact Bool.noConfusion hns
      refine ⟨?_, fun x hx => ?_, fun p => ⟨?_, ?_⟩⟩
      · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.2 ⟨hnd, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun a ha b hb => ?_⟩
        rw [List.mem_singleton] at hb
        subst hb
        exact fun e => hnot (e ▸ ha)
      · simp only [Array.toList_push, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with hx | rfl
        · exact ⟨(hmem x hx).1, by have := (hmem x hx).2.1; omega, (hmem x hx).2.2⟩
        · exact ⟨hlt, by simp, rfl⟩
      · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · rintro (h | rfl)
          · obtain ⟨hp, a, ha, e⟩ := (hiff p).1.1 h
            exact ⟨hp, a, by omega, e⟩
          · exact ⟨hlt, j, by omega, rfl⟩
        · rintro ⟨hp, a, ha, e⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
          · exact Or.inl ((hiff p).1.2 ⟨hp, a, ha, e⟩)
          · exact Or.inr e.symm
      · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Std.HashMap.contains_insert,
          Bool.or_eq_true, beq_iff_eq]
        rw [(hiff p).2]
        exact ⟨fun h => h.elim (fun e => Or.inr e.symm) Or.inl,
          fun h => h.elim Or.inr fun e => Or.inl e.symm⟩
    · rw [if_neg hc]
      refine ⟨hnd, fun x hx => ⟨(hmem x hx).1, by have := (hmem x hx).2.1; omega,
        (hmem x hx).2.2⟩, fun p => ⟨?_, (hiff p).2⟩⟩
      constructor
      · intro h
        obtain ⟨hp, a, ha, e⟩ := (hiff p).1.1 h
        exact ⟨hp, a, by omega, e⟩
      · rintro ⟨hp, a, ha, e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
        · exact (hiff p).1.2 ⟨hp, a, ha, e⟩
        · subst e
          refine (hiff _).2.1 ?_
          by_contra hn
          exact hc ⟨hp, by simpa using hn⟩
  · refine ⟨List.nodup_nil, fun x hx => absurd hx List.not_mem_nil, fun p => ⟨?_, ?_⟩⟩
    · simp
    · simp

theorem labOf_spec (used : Array Bool) (target : Array Nat) (sz : Nat) :
    (labOf used target sz < target.size ∧ used[labOf used target sz]! = false ∧
        target[labOf used target sz]! = sz ∧
        ∀ i < labOf used target sz, ¬ (used[i]! = false ∧ target[i]! = sz)) ∨
      (labOf used target sz = target.size ∧
        ∀ i < target.size, ¬ (used[i]! = false ∧ target[i]! = sz)) := by
  have key := CFSG.KS.BfsReplay.forIn_range'_yield target.size 0 target.size
    (bodyL used target sz)
    (fun j l => (l < j ∧ used[l]! = false ∧ target[l]! = sz ∧
        ∀ i < l, ¬ (used[i]! = false ∧ target[i]! = sz)) ∨
      (l = target.size ∧ ∀ i < j, ¬ (used[i]! = false ∧ target[i]! = sz)))
    (fun j hj l hP => ?_) (Or.inr ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩)
  · rcases key with h | h
    · exact Or.inl h
    · exact Or.inr h
  · refine ⟨_, by rw [Nat.zero_add, bodyL_eq], ?_⟩
    rcases hP with ⟨hl, h1, h2, h3⟩ | ⟨hl, h1⟩
    · rw [if_neg (fun h => by omega)]
      exact Or.inl ⟨by omega, h1, h2, h3⟩
    · by_cases hg : used[j]! = false ∧ target[j]! = sz
      · rw [if_pos ⟨hl, hg⟩]
        exact Or.inl ⟨by omega, hg.1, hg.2, h1⟩
      · rw [if_neg (fun h => hg h.2)]
        refine Or.inr ⟨hl, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h1 i hi
        · exact hg

theorem forIn_bodyS_cons (l : Nat) (x : Nat × Nat) (L : List (Nat × Nat)) (lab wit : Array Nat) :
    Id.run (forIn (x :: L) (lab, wit) (bodyS l)) =
      Id.run (forIn L (lab.set! x.1 l, wit.set! x.1 x.2) (bodyS l)) := by
  simp only [List.forIn_cons, bodyS_eq, pure_bind]

theorem setOf_list (l : Nat) : ∀ (L : List (Nat × Nat)) (lab wit : Array Nat),
    lab.size = wit.size →
    (Id.run (forIn L (lab, wit) (bodyS l))).1.size = lab.size ∧
      (Id.run (forIn L (lab, wit) (bodyS l))).2.size = wit.size ∧ ∀ q,
      (q ∈ L.map Prod.fst → q < lab.size →
        (Id.run (forIn L (lab, wit) (bodyS l))).1[q]! = l ∧
          (q, (Id.run (forIn L (lab, wit) (bodyS l))).2[q]!) ∈ L) ∧
      (q ∉ L.map Prod.fst → (Id.run (forIn L (lab, wit) (bodyS l))).1[q]! = lab[q]! ∧
        (Id.run (forIn L (lab, wit) (bodyS l))).2[q]! = wit[q]!)
  | [], lab, wit, _ => ⟨rfl, rfl, fun q => ⟨fun h => absurd h List.not_mem_nil,
      fun _ => ⟨rfl, rfl⟩⟩⟩
  | x :: L, lab, wit, hs => by
    rw [forIn_bodyS_cons]
    obtain ⟨h1, h2, h3⟩ := setOf_list l L (lab.set! x.1 l) (wit.set! x.1 x.2)
      (by rw [Array.size_set!, Array.size_set!, hs])
    rw [Array.size_set!] at h1 h2
    refine ⟨h1, h2, fun q => ⟨fun hq hql => ?_, fun hq => ?_⟩⟩
    · by_cases hL : q ∈ L.map Prod.fst
      · obtain ⟨e1, e2⟩ := (h3 q).1 hL (by rw [Array.size_set!]; exact hql)
        exact ⟨e1, List.mem_cons_of_mem _ e2⟩
      · obtain ⟨e1, e2⟩ := (h3 q).2 hL
        have hqx : q = x.1 := by
          rw [List.map_cons, List.mem_cons] at hq
          exact hq.resolve_right hL
        subst hqx
        rw [e1, e2, Array.getElem!_set!_self _ _ _ hql,
          Array.getElem!_set!_self _ _ _ (by rw [← hs]; exact hql)]
        exact ⟨rfl, List.mem_cons_self⟩
    · rw [List.map_cons, List.mem_cons, not_or] at hq
      obtain ⟨e1, e2⟩ := (h3 q).2 hq.2
      rw [e1, e2, Array.getElem!_set!_ne _ _ _ _ (Ne.symm hq.1),
        Array.getElem!_set!_ne _ _ _ _ (Ne.symm hq.1)]
      exact ⟨rfl, rfl⟩

theorem setOf_spec (cls : Array (Nat × Nat)) (l : Nat) (lab wit : Array Nat)
    (hs : lab.size = wit.size) :
    (setOf cls l lab wit).1.size = lab.size ∧ (setOf cls l lab wit).2.size = wit.size ∧ ∀ q,
      (q ∈ cls.toList.map Prod.fst → q < lab.size → (setOf cls l lab wit).1[q]! = l ∧
        (q, (setOf cls l lab wit).2[q]!) ∈ cls.toList) ∧
      (q ∉ cls.toList.map Prod.fst → (setOf cls l lab wit).1[q]! = lab[q]! ∧
        (setOf cls l lab wit).2[q]! = wit[q]!) := by
  unfold setOf
  rw [← Array.forIn_toList]
  exact setOf_list l cls.toList lab wit hs

def Vis (c : Nat → Nat) (j l : Nat) : Prop := ∃ k < j, c k = l

theorem vis_succ {c : Nat → Nat} {j l : Nat} : Vis c (j + 1) l ↔ Vis c j l ∨ c j = l := by
  constructor
  · rintro ⟨k, hk, e⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · exact Or.inl ⟨k, h, e⟩
    · exact Or.inr (h ▸ e)
  · rintro (⟨k, hk, e⟩ | e)
    · exact ⟨k, by omega, e⟩
    · exact ⟨j, by omega, e⟩

structure ClassHyp (m : Nat) (target : Array Nat) (cj : Nat → Nat → Nat) (c : Nat → Nat) :
    Prop where
  pos : 0 < m
  lt : ∀ k < m, c k < target.size
  surj : ∀ l < target.size, ∃ k < m, c k = l
  orb : ∀ k < m, ∀ p < m, (c p = c k ↔ ∃ a < m, cj a k = p)
  cnt : ∀ l < target.size, ((Finset.range m).filter fun k => c k = l).card = target[l]!
  zero : c 0 = 0

structure OInv (m : Nat) (target : Array Nat) (cj : Nat → Nat → Nat) (c : Nat → Nat) (j : Nat)
    (σ : Nat → Nat) (s : CSt) : Prop where
  szl : s.1.size = m
  szw : s.2.1.size = m
  szr : s.2.2.1.size = target.size
  szu : s.2.2.2.size = target.size
  labv : ∀ p < m, Vis c j (c p) → s.1[p]! = σ (c p)
  labn : ∀ p < m, ¬ Vis c j (c p) → s.1[p]! = m
  sig : ∀ l, Vis c j l → σ l < target.size ∧ target[σ l]! = target[l]! ∧
    s.2.2.1[σ l]! < m ∧ c s.2.2.1[σ l]! = l
  wit : ∀ p < m, Vis c j (c p) → s.2.1[p]! < m ∧ cj s.2.1[p]! s.2.2.1[σ (c p)]! = p
  inj : ∀ l l', Vis c j l → Vis c j l' → σ l = σ l' → l = l'
  used : ∀ i < target.size, s.2.2.2[i]! = true ↔ ∃ l, Vis c j l ∧ σ l = i
  zero : 0 < j → σ 0 = 0

variable {m : Nat} {target : Array Nat} {cj : Nat → Nat → Nat} {c : Nat → Nat}

theorem ClassHyp.size_le (H : ClassHyp m target cj c) : target.size ≤ m := by
  classical
  have hsub : Finset.range target.size ⊆ (Finset.range m).image c := fun l hl => by
    obtain ⟨k, hk, e⟩ := H.surj l (Finset.mem_range.1 hl)
    exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, e⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  simpa using this

theorem ClassHyp.mem_clsOf (H : ClassHyp m target cj c) {k : Nat} (hk : k < m) (p : Nat) :
    p ∈ (clsOf m cj k).toList.map Prod.fst ↔ p < m ∧ c p = c k := by
  rw [(clsOf_spec m cj k).2.2]
  constructor
  · rintro ⟨hp, a, ha, e⟩
    exact ⟨hp, (H.orb k hk p hp).2 ⟨a, ha, e⟩⟩
  · rintro ⟨hp, e⟩
    exact ⟨hp, (H.orb k hk p hp).1 e⟩

theorem ClassHyp.size_clsOf (H : ClassHyp m target cj c) {k : Nat} (hk : k < m) :
    (clsOf m cj k).size = target[c k]! := by
  classical
  have hlen : (clsOf m cj k).size = ((clsOf m cj k).toList.map Prod.fst).length := by simp
  rw [hlen, ← H.cnt (c k) (H.lt k hk), ← List.toFinset_card_of_nodup (clsOf_spec m cj k).1]
  congr 1
  ext p
  rw [List.mem_toFinset, H.mem_clsOf hk, Finset.mem_filter, Finset.mem_range]

theorem OInv.mono {j j' : Nat} {σ : Nat → Nat} {s : CSt} (I : OInv m target cj c j σ s)
    (hV : ∀ l, Vis c j' l ↔ Vis c j l) (h0 : 0 < j' → 0 < j) : OInv m target cj c j' σ s where
  szl := I.szl
  szw := I.szw
  szr := I.szr
  szu := I.szu
  labv p hp h := I.labv p hp ((hV _).1 h)
  labn p hp h := I.labn p hp fun h' => h ((hV _).2 h')
  sig l h := I.sig l ((hV l).1 h)
  wit p hp h := I.wit p hp ((hV _).1 h)
  inj l l' h h' := I.inj l l' ((hV l).1 h) ((hV l').1 h')
  used i hi := (I.used i hi).trans
    ⟨fun ⟨l, h1, h2⟩ => ⟨l, (hV l).2 h1, h2⟩, fun ⟨l, h1, h2⟩ => ⟨l, (hV l).1 h1, h2⟩⟩
  zero h := I.zero (h0 h)

theorem oInv_init (m : Nat) (target : Array Nat) (cj : Nat → Nat → Nat) (c : Nat → Nat) :
    OInv m target cj c 0 id (Array.replicate m m, Array.replicate m 0,
      Array.replicate target.size 0, Array.replicate target.size false) where
  szl := Array.size_replicate
  szw := Array.size_replicate
  szr := Array.size_replicate
  szu := Array.size_replicate
  labv _ _ h := absurd h fun ⟨k, hk, _⟩ => Nat.not_lt_zero k hk
  labn p hp _ := by
    rw [getElem!_pos _ p (by simpa using hp)]
    simp
  sig _ h := absurd h fun ⟨k, hk, _⟩ => Nat.not_lt_zero k hk
  wit _ _ h := absurd h fun ⟨k, hk, _⟩ => Nat.not_lt_zero k hk
  inj _ _ h := absurd h fun ⟨k, hk, _⟩ => Nat.not_lt_zero k hk
  used i hi := by
    rw [getElem!_pos _ i (by simpa using hi)]
    simp only [Array.getElem_replicate, Bool.false_eq_true, false_iff]
    exact fun ⟨_, ⟨k, hk, _⟩, _⟩ => Nat.not_lt_zero k hk
  zero h := absurd h (Nat.lt_irrefl 0)

theorem OInv.exists_unused (H : ClassHyp m target cj c) {j : Nat} (hj : j < m)
    {σ : Nat → Nat} {s : CSt} (I : OInv m target cj c j σ s) (hv : ¬ Vis c j (c j)) :
    ∃ i < target.size, s.2.2.2[i]! = false ∧ target[i]! = target[c j]! := by
  classical
  by_contra hne
  have hall : ∀ i < target.size, target[i]! = target[c j]! → s.2.2.2[i]! = true :=
    fun i hi ht => by
      cases hb : s.2.2.2[i]! with
      | false => exact absurd ⟨i, hi, hb, ht⟩ hne
      | true => rfl
  set A := (Finset.range target.size).filter fun i => target[i]! = target[c j]! with hA
  set A' := A.filter fun l => Vis c j l with hA'
  have hsub : A ⊆ A'.image σ := fun i hi => by
    obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
    obtain ⟨l1, hv1, e⟩ := (I.used i (Finset.mem_range.1 hi1)).1
      (hall i (Finset.mem_range.1 hi1) hi2)
    refine Finset.mem_image.2 ⟨l1, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨?_, ?_⟩, hv1⟩, e⟩
    · obtain ⟨k, hk, rfl⟩ := hv1
      exact Finset.mem_range.2 (H.lt k (by omega))
    · rw [← (I.sig l1 hv1).2.1, e]
      exact hi2
  have hss : A' ⊂ A := Finset.filter_ssubset.2
    ⟨c j, Finset.mem_filter.2 ⟨Finset.mem_range.2 (H.lt j hj), rfl⟩, hv⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := A') (f := σ)
  have h3 := Finset.card_lt_card hss
  omega

theorem oInv_step (H : ClassHyp m target cj c) {j : Nat} (hj : j < m) {σ : Nat → Nat}
    {s : CSt} (I : OInv m target cj c j σ s) :
    ∃ s', bodyK m cj target j s = pure (ForInStep.yield s') ∧
      ∃ σ', OInv m target cj c (j + 1) σ' s' := by
  have hns := H.size_le
  rw [bodyK_eq]
  by_cases hv : Vis c j (c j)
  · have hlab : s.1[j]! ≠ m := by
      rw [I.labv j hj hv]
      have := (I.sig _ hv).1
      omega
    rw [if_neg (by rwa [beq_iff_eq])]
    refine ⟨_, rfl, σ, ?_⟩
    have hV : ∀ l, Vis c (j + 1) l ↔ Vis c j l := fun l => by
      rw [vis_succ]
      exact ⟨fun h => h.elim id fun e => e ▸ hv, Or.inl⟩
    have hj0 : 0 < j := by
      obtain ⟨k, hk, -⟩ := hv
      omega
    exact I.mono hV fun _ => hj0
  · have hlab : s.1[j]! = m := I.labn j hj hv
    rw [if_pos (by rw [beq_iff_eq]; exact hlab)]
    have hsz := H.size_clsOf hj
    have hmem := (clsOf_spec m cj j).2.1
    obtain ⟨i0, hi0, hu0, ht0⟩ := I.exists_unused H hj hv
    obtain ⟨hlt, hlu, hlt', hlmin⟩ :
        labOf s.2.2.2 target (clsOf m cj j).size < target.size ∧
          s.2.2.2[labOf s.2.2.2 target (clsOf m cj j).size]! = false ∧
          target[labOf s.2.2.2 target (clsOf m cj j).size]! = (clsOf m cj j).size ∧
          ∀ i < labOf s.2.2.2 target (clsOf m cj j).size,
            ¬ (s.2.2.2[i]! = false ∧ target[i]! = (clsOf m cj j).size) := by
      rcases labOf_spec s.2.2.2 target (clsOf m cj j).size with h | h
      · exact h
      · exact absurd ⟨hu0, ht0.trans hsz.symm⟩ (h.2 i0 hi0)
    rw [if_pos hlt]
    refine ⟨_, rfl, ?_⟩
    generalize hl : labOf s.2.2.2 target (clsOf m cj j).size = l at hlt hlu hlt' hlmin
    obtain ⟨hR1, hR2, hR3⟩ := setOf_spec (clsOf m cj j) l s.1 s.2.1 (I.szl.trans I.szw.symm)
    have hne : ∀ l1, Vis c j l1 → σ l1 ≠ l := fun l1 h1 e => by
      have := (I.used (σ l1) (I.sig l1 h1).1).2 ⟨l1, h1, rfl⟩
      rw [e, hlu] at this
      exact Bool.noConfusion this
    have hvj : ∀ l1, Vis c j l1 → l1 ≠ c j := fun l1 h1 e => hv (e ▸ h1)
    refine ⟨fun x => if x = c j then l else σ x, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    all_goals try dsimp only
    · exact hR1.trans I.szl
    · exact hR2.trans I.szw
    · exact (Array.size_set! _ _ _).trans I.szr
    · exact (Array.size_set! _ _ _).trans I.szu
    · intro p hp hvp
      by_cases hcp : c p = c j
      · rw [if_pos hcp]
        exact ((hR3 p).1 ((H.mem_clsOf hj p).2 ⟨hp, hcp⟩) (by rw [I.szl]; exact hp)).1
      · have hvp' : Vis c j (c p) := (vis_succ.1 hvp).resolve_right fun e => hcp e.symm
        rw [if_neg hcp, ((hR3 p).2 fun h => hcp ((H.mem_clsOf hj p).1 h).2).1]
        exact I.labv p hp hvp'
    · intro p hp hvp
      rw [vis_succ, not_or] at hvp
      rw [((hR3 p).2 fun h => hvp.2 ((H.mem_clsOf hj p).1 h).2.symm).1]
      exact I.labn p hp hvp.1
    · intro l1 hv1
      by_cases h1 : l1 = c j
      · rw [if_pos h1, Array.getElem!_set!_self _ _ _ (by rw [I.szr]; exact hlt)]
        exact ⟨hlt, by rw [hlt', hsz, h1], hj, h1.symm⟩
      · have hv1' : Vis c j l1 := (vis_succ.1 hv1).resolve_right fun e => h1 e.symm
        rw [if_neg h1, Array.getElem!_set!_ne _ _ _ _ (Ne.symm (hne l1 hv1'))]
        exact I.sig l1 hv1'
    · intro p hp hvp
      by_cases hcp : c p = c j
      · obtain ⟨e1, e2⟩ := (hR3 p).1 ((H.mem_clsOf hj p).2 ⟨hp, hcp⟩) (by rw [I.szl]; exact hp)
        have hw := hmem _ e2
        rw [if_pos hcp, Array.getElem!_set!_self _ _ _ (by rw [I.szr]; exact hlt)]
        exact ⟨hw.2.1, hw.2.2⟩
      · have hvp' : Vis c j (c p) := (vis_succ.1 hvp).resolve_right fun e => hcp e.symm
        rw [if_neg hcp, ((hR3 p).2 fun h => hcp ((H.mem_clsOf hj p).1 h).2).2,
          Array.getElem!_set!_ne _ _ _ _ (Ne.symm (hne _ hvp'))]
        exact I.wit p hp hvp'
    · intro l1 l2 hv1 hv2 e
      by_cases h1 : l1 = c j <;> by_cases h2 : l2 = c j
      · rw [h1, h2]
      · have hv2' : Vis c j l2 := (vis_succ.1 hv2).resolve_right fun e => h2 e.symm
        rw [if_pos h1, if_neg h2] at e
        exact absurd e.symm (hne l2 hv2')
      · have hv1' : Vis c j l1 := (vis_succ.1 hv1).resolve_right fun e => h1 e.symm
        rw [if_neg h1, if_pos h2] at e
        exact absurd e (hne l1 hv1')
      · have hv1' : Vis c j l1 := (vis_succ.1 hv1).resolve_right fun e => h1 e.symm
        have hv2' : Vis c j l2 := (vis_succ.1 hv2).resolve_right fun e => h2 e.symm
        rw [if_neg h1, if_neg h2] at e
        exact I.inj l1 l2 hv1' hv2' e
    · intro i hi
      by_cases hil : i = l
      · subst hil
        rw [Array.getElem!_set!_self _ _ _ (by rw [I.szu]; exact hlt)]
        exact ⟨fun _ => ⟨c j, vis_succ.2 (Or.inr rfl), if_pos rfl⟩, fun _ => rfl⟩
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hil), I.used i hi]
        constructor
        · rintro ⟨l1, hv1, e⟩
          exact ⟨l1, vis_succ.2 (Or.inl hv1), by rw [if_neg (hvj l1 hv1)]; exact e⟩
        · rintro ⟨l1, hv1, e⟩
          by_cases h1 : l1 = c j
          · rw [if_pos h1] at e
            exact absurd e.symm hil
          · exact ⟨l1, (vis_succ.1 hv1).resolve_right fun e' => h1 e'.symm,
              by rw [if_neg h1] at e; exact e⟩
    · intro _
      by_cases hj0 : j = 0
      · subst hj0
        have hc0 : c 0 = 0 := H.zero
        rw [if_pos hc0.symm]
        by_contra hl0
        refine hlmin 0 (by omega) ⟨?_, ?_⟩
        · have h0 := I.used 0 (by have := H.lt 0 H.pos; omega)
          cases hb : s.2.2.2[0]! with
          | false => rfl
          | true =>
            obtain ⟨_, ⟨k, hk, _⟩, _⟩ := h0.1 hb
            exact absurd hk (Nat.not_lt_zero k)
        · rw [hsz, hc0]
      · have hv0 : Vis c j 0 := ⟨0, by omega, H.zero⟩
        rw [if_neg (fun e : 0 = c j => hv (e ▸ hv0))]
        exact I.zero (by omega)

theorem classLoopN_spec (H : ClassHyp m target cj c) :
    ∃ σ : Nat → Nat, (∀ l < target.size, σ l < target.size ∧ target[σ l]! = target[l]!) ∧
      (∀ l < target.size, ∀ l' < target.size, σ l = σ l' → l = l') ∧ σ 0 = 0 ∧
      (classLoopN m cj target).reps.size = target.size ∧
      (∀ k < m, (classLoopN m cj target).lab[k]! = σ (c k)) ∧
      (∀ l < target.size, (classLoopN m cj target).reps[σ l]! < m ∧
        c (classLoopN m cj target).reps[σ l]! = l) ∧
      ∀ k < m, (classLoopN m cj target).wit[k]! < m ∧
        cj (classLoopN m cj target).wit[k]! (classLoopN m cj target).reps[σ (c k)]! = k := by
  obtain ⟨σ, I⟩ := CFSG.KS.BfsReplay.forIn_range'_yield m 0 (Array.replicate m m,
      Array.replicate m 0, Array.replicate target.size 0, Array.replicate target.size false)
    (bodyK m cj target) (fun j s => ∃ σ, OInv m target cj c j σ s)
    (fun j hj s ⟨_, I⟩ => by rw [Nat.zero_add]; exact oInv_step H hj I) ⟨id, oInv_init m target cj c⟩
  rw [classLoopN_eq]
  have hV : ∀ l, Vis c m l ↔ l < target.size := fun l =>
    ⟨fun ⟨k, hk, e⟩ => e ▸ H.lt k hk, fun hl => H.surj l hl⟩
  refine ⟨σ, fun l hl => ⟨(I.sig l ((hV l).2 hl)).1, (I.sig l ((hV l).2 hl)).2.1⟩,
    fun l hl l' hl' e => I.inj l l' ((hV l).2 hl) ((hV l').2 hl') e, I.zero H.pos, I.szr,
    fun k hk => I.labv k hk ((hV _).2 (H.lt k hk)), fun l hl => (I.sig l ((hV l).2 hl)).2.2,
    fun k hk => I.wit k hk ((hV _).2 (H.lt k hk))⟩

section Checks

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (fget)

variable {n w : Nat}

private theorem pcomp_pidn_l' {x : Nat} (hx : canonK n w (mask w) (n * w) x = true) :
    pcomp n w (mask w) (pidn n w) x = x := by
  have hsz := canon_sz hx
  exact eq_of_pg (CFSG.KC.BfsPin.canonK_pcomp (canon_pidn hsz) hx) hx fun i hi => by
    rw [pg_pcomp' (canon_pidn hsz) hi, pg_pidn' hsz (canon_lt hx hi)]

private theorem pcomp_pidn_r' {x : Nat} (hx : canonK n w (mask w) (n * w) x = true) :
    pcomp n w (mask w) x (pidn n w) = x := by
  have hsz := canon_sz hx
  exact eq_of_pg (CFSG.KC.BfsPin.canonK_pcomp hx (canon_pidn hsz)) hx fun i hi => by
    rw [pg_pcomp' hx hi, pg_pidn' hsz hi]

private theorem pcomp_cancel' {x y z : Nat} (hx : canonK n w (mask w) (n * w) x = true)
    (hy : canonK n w (mask w) (n * w) y = true) (hz : canonK n w (mask w) (n * w) z = true)
    (h : pcomp n w (mask w) y x = pidn n w) :
    pcomp n w (mask w) y (pcomp n w (mask w) x z) = z := by
  rw [← pcomp_assoc' hy hx hz, h, pcomp_pidn_l' hz]

private theorem inv_unique' {x y z : Nat} (hx : canonK n w (mask w) (n * w) x = true)
    (hy : canonK n w (mask w) (n * w) y = true) (hz : canonK n w (mask w) (n * w) z = true)
    (h1 : pcomp n w (mask w) y x = pidn n w) (h2 : pcomp n w (mask w) x z = pidn n w) : y = z :=
  calc y = pcomp n w (mask w) y (pcomp n w (mask w) x z) := by rw [h2, pcomp_pidn_r' hy]
    _ = z := pcomp_cancel' hx hy hz h1

private theorem cntR_zero' (f : Nat → Bool) (N : Nat) :
    CFSG.KC.HeAutK.cntR f 0 N = ((List.range N).filter f).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [CFSG.KC.HeAutK.cntR_succ, ih, Nat.zero_add, List.range_succ, List.filter_append,
      List.length_append]
    cases h : f N <;> simp [h]

private theorem length_filter_range_card (m : Nat) (f : Nat → Bool) :
    ((List.range m).filter f).length = ((Finset.range m).filter fun k => f k = true).card := by
  show _ = Multiset.card (Multiset.filter (fun k => f k = true) (Multiset.range m))
  rw [← Multiset.coe_range, Multiset.filter_coe, Multiset.coe_card]
  simp only [Bool.decide_eq_true]

private theorem groupK_facts {m : Nat} {CT CI Q : Nat → Nat} (hg : groupK n w m CT CI Q = true) :
    (∀ a < m, canonK n w (mask w) (n * w) (CT a) = true ∧
      canonK n w (mask w) (n * w) (CI a) = true ∧ pcomp n w (mask w) (CI a) (CT a) = pidn n w) ∧
    ∀ a < m, ∀ b < m, (a = b ∨ CT a ≠ CT b) ∧ fget (Q a) b 8 < m ∧
      CT (fget (Q a) b 8) = pcomp n w (mask w) (CT a) (CT b) := by
  unfold groupK at hg
  rw [strictB_app] at hg
  obtain ⟨h1, h2⟩ := andB_iff.1 hg
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_⟩
  · obtain ⟨h3, h4⟩ := andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h1 a ha)
    obtain ⟨h5, h6⟩ := andB_iff.1 h4
    exact ⟨h3, h5, Nat.eq_of_beq_eq_true h6⟩
  · have h3 := CFSG.KS.Raw.Orb.allN_iff.1 h2 a ha
    rw [strictB_app, strictB_app] at h3
    have h4 := CFSG.KS.Raw.Orb.allN_iff.1 h3 b hb
    rw [strictB_app, strictB_app] at h4
    obtain ⟨h5, h6⟩ := andB_iff.1 h4
    obtain ⟨h7, h8⟩ := andB_iff.1 h6
    refine ⟨?_, Nat.blt_eq.mp h7, Nat.eq_of_beq_eq_true h8⟩
    rcases orB_iff.1 h5 with h9 | h9
    · exact Or.inl (Nat.eq_of_beq_eq_true h9)
    · exact Or.inr (Nat.ne_of_beq_eq_false (notB_iff.1 h9))

private theorem classK_facts {m ns lab rep wit SZ : Nat} {CT CI P : Nat → Nat}
    (h : classK n w m CT CI P lab rep wit SZ ns = true) :
    (∀ k < m, ∀ a < m, fget (P k) a 8 < m ∧
      CT (fget (P k) a 8) = pcomp n w (mask w) (CT a) (pcomp n w (mask w) (CT k) (CI a)) ∧
      fget lab (fget (P k) a 8) 8 = fget lab k 8) ∧
    (∀ l < ns, fget rep l 8 < m ∧ fget lab (fget rep l 8) 8 = l) ∧
    (∀ k < m, fget lab k 8 < ns ∧ fget wit k 8 < m ∧
      pcomp n w (mask w) (CT (fget wit k 8))
        (pcomp n w (mask w) (CT (fget rep (fget lab k 8) 8)) (CI (fget wit k 8))) = CT k) ∧
    (∀ l < ns, CFSG.KC.HeAutK.cntR (fun k => Nat.beq (fget lab k 8) l) 0 m = fget SZ l 8) ∧
    0 < m ∧ CT 0 = pidn n w ∧ fget lab 0 8 = 0 := by
  unfold classK at h
  rw [strictB_app] at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h7⟩ := andB_iff.1 h
  refine ⟨fun k hk a ha => ?_, fun l hl => ?_, fun k hk => ?_,
    fun l hl => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 h4 l hl), Nat.blt_eq.mp h5,
    Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7⟩
  · have h8 := CFSG.KS.Raw.Orb.allN_iff.1 h1 k hk
    rw [strictB_app, strictB_app, strictB_app] at h8
    have h9 := CFSG.KS.Raw.Orb.allN_iff.1 h8 a ha
    rw [strictB_app] at h9
    obtain ⟨h10, h11⟩ := andB_iff.1 h9
    obtain ⟨h12, h13⟩ := andB_iff.1 h11
    exact ⟨Nat.blt_eq.mp h10, Nat.eq_of_beq_eq_true h12, Nat.eq_of_beq_eq_true h13⟩
  · have h8 := CFSG.KS.Raw.Orb.allN_iff.1 h2 l hl
    rw [strictB_app] at h8
    obtain ⟨h9, h10⟩ := andB_iff.1 h8
    exact ⟨Nat.blt_eq.mp h9, Nat.eq_of_beq_eq_true h10⟩
  · have h8 := CFSG.KS.Raw.Orb.allN_iff.1 h3 k hk
    rw [strictB_app, strictB_app] at h8
    obtain ⟨h9, h10⟩ := andB_iff.1 h8
    obtain ⟨h11, h12⟩ := andB_iff.1 h10
    exact ⟨Nat.blt_eq.mp h9, Nat.blt_eq.mp h11, Nat.eq_of_beq_eq_true h12⟩

private theorem classOK_of_tabs {m ns lab rep wit SZ : Nat} {CT CI Q P : Nat → Nat}
    {sizes : Array Nat} {T : Array Tab} (hTs : T.size = m)
    (hTg : ∀ i < m, T[i]! = unpack n w (CT i))
    (hz : sizes.size = ns ∧ ∀ l < ns, sizes[l]! = fget SZ l 8)
    (hg : groupK n w m CT CI Q = true) (h : classK n w m CT CI P lab rep wit SZ ns = true) :
    classOK n T (T.map (invTab n)) (classData n T sizes) sizes = true := by
  obtain ⟨hcan, hQ⟩ := groupK_facts hg
  obtain ⟨hP, hrep, hwit, hcnt, hm, h0, hlab0⟩ := classK_facts h
  have hCT : ∀ a < m, canonK n w (mask w) (n * w) (CT a) = true := fun a ha => (hcan a ha).1
  have hCI : ∀ a < m, canonK n w (mask w) (n * w) (CI a) = true := fun a ha => (hcan a ha).2.1
  have hli : ∀ a < m, pcomp n w (mask w) (CI a) (CT a) = pidn n w := fun a ha => (hcan a ha).2.2
  have hri : ∀ a < m, pcomp n w (mask w) (CT a) (CI a) = pidn n w := fun a ha =>
    pcomp_inv_of_pcomp (hCI a ha) (hCT a ha) (hli a ha)
  have hsz : szOK n w = true := canon_sz (hCT 0 hm)
  have hinj : ∀ a < m, ∀ b < m, CT a = CT b → a = b := fun a ha b hb e =>
    (hQ a ha b hb).1.resolve_right fun hne => hne e
  have hinv : ∀ v < m, ∃ b < m, CT b = CI v := by
    intro v hv
    let f : Fin m → Fin m := fun b => ⟨fget (Q v) b 8, (hQ v hv b b.2).2.1⟩
    have hf : Function.Injective f := by
      intro b b' e
      have e1 : CT (fget (Q v) b 8) = CT (fget (Q v) b' 8) := congrArg CT (congrArg Fin.val e)
      rw [(hQ v hv b b.2).2.2, (hQ v hv b' b'.2).2.2] at e1
      have e2 := congrArg (pcomp n w (mask w) (CI v)) e1
      rw [pcomp_cancel' (hCT v hv) (hCI v hv) (hCT b b.2) (hli v hv),
        pcomp_cancel' (hCT v hv) (hCI v hv) (hCT b' b'.2) (hli v hv)] at e2
      exact Fin.ext (hinj b b.2 b' b'.2 e2)
    obtain ⟨b, hb⟩ := Finite.surjective_of_injective hf ⟨0, hm⟩
    have e1 : CT (fget (Q v) b 8) = CT 0 := congrArg CT (congrArg Fin.val hb)
    rw [(hQ v hv b b.2).2.2, h0] at e1
    exact ⟨b, b.2, (inv_unique' (hCT v hv) (hCI v hv) (hCT b b.2) (hli v hv) e1).symm⟩
  have hQi : ∀ a < m, ∀ b < m, CI (fget (Q a) b 8) = pcomp n w (mask w) (CI b) (CI a) := by
    intro a ha b hb
    have hq := (hQ a ha b hb).2.1
    refine inv_unique' (hCT _ hq) (hCI _ hq)
      (CFSG.KC.BfsPin.canonK_pcomp (hCI b hb) (hCI a ha)) (hli _ hq) ?_
    rw [(hQ a ha b hb).2.2, pcomp_assoc' (hCT a ha) (hCT b hb)
        (CFSG.KC.BfsPin.canonK_pcomp (hCI b hb) (hCI a ha)),
      ← pcomp_assoc' (hCT b hb) (hCI b hb) (hCI a ha), hri b hb, pcomp_pidn_l' (hCI a ha),
      hri a ha]
  have hPP : ∀ k < m, ∀ a < m, ∀ b < m,
      fget (P (fget (P k) b 8)) a 8 = fget (P k) (fget (Q a) b 8) 8 := by
    intro k hk a ha b hb
    have hkb := (hP k hk b hb).1
    have hq := (hQ a ha b hb).2.1
    refine hinj _ (hP _ hkb a ha).1 _ (hP k hk _ hq).1 ?_
    rw [(hP _ hkb a ha).2.1, (hP k hk b hb).2.1, (hP k hk _ hq).2.1, (hQ a ha b hb).2.2,
      hQi a ha b hb,
      pcomp_assoc' (hCT a ha) (hCT b hb) (CFSG.KC.BfsPin.canonK_pcomp (hCT k hk)
        (CFSG.KC.BfsPin.canonK_pcomp (hCI b hb) (hCI a ha))),
      pcomp_assoc' (hCT b hb) (CFSG.KC.BfsPin.canonK_pcomp (hCT k hk) (hCI b hb)) (hCI a ha),
      pcomp_assoc' (hCT k hk) (hCI b hb) (hCI a ha)]
  have hPinv : ∀ r < m, ∀ v < m, ∀ b < m, CT b = CI v → fget (P (fget (P r) v 8)) b 8 = r := by
    intro r hr v hv b hb e
    have hrv := (hP r hr v hv).1
    have e' : CI b = CT v := inv_unique' (hCT b hb) (hCI b hb) (hCT v hv) (hli b hb)
      (by rw [e]; exact hli v hv)
    refine hinj _ (hP _ hrv b hb).1 r hr ?_
    rw [(hP _ hrv b hb).2.1, (hP r hr v hv).2.1, e, e',
      pcomp_assoc' (hCT v hv) (CFSG.KC.BfsPin.canonK_pcomp (hCT r hr) (hCI v hv)) (hCT v hv),
      pcomp_assoc' (hCT r hr) (hCI v hv) (hCT v hv), hli v hv, pcomp_pidn_r' (hCT r hr),
      pcomp_cancel' (hCT v hv) (hCI v hv) (hCT r hr) (hli v hv)]
  have hPk : ∀ k < m, fget (P (fget rep (fget lab k 8) 8)) (fget wit k 8) 8 = k := fun k hk => by
    obtain ⟨hl, hv, e⟩ := hwit k hk
    have hr := (hrep _ hl).1
    exact hinj _ (hP _ hr _ hv).1 k hk ((hP _ hr _ hv).2.1.trans e)
  obtain ⟨hinvT, hinvs⟩ := invsOK_of_pcomp (G := CT) (GI := CI) hTs hTg
    fun k hk => ⟨hCT k hk, hCI k hk, hri k hk⟩
  have hinjT : ∀ a < T.size, ∀ b < T.size, T[a]! = T[b]! → a = b := by
    intro a ha b hb e
    rw [hTs] at ha hb
    rw [hTg a ha, hTg b hb] at e
    exact hinj a ha b hb (unpack_inj' (hCT a ha) (hCT b hb) e)
  have hpos : ∀ i < m, posOf (indexOf T) T T[i]! = i := fun i hi =>
    (CFSG.KS.BfsReplay.indexOf_spec hinjT).1 i (hTs ▸ hi)
  have hfound : ∀ p < m, found (indexOf T) T T[p]! = true := fun p hp => by
    unfold found
    rw [hpos p hp]
    simp [hTs, hp]
  have hconj : ∀ k < m, ∀ a < m,
      conjTab n T[a]! (T.map (invTab n))[a]! T[k]! = T[fget (P k) a 8]! := by
    intro k hk a ha
    rw [hTg _ (hP k hk a ha).1, (hP k hk a ha).2.1, hTg a ha, hTg k hk, hinvT a ha]
    unfold conjTab
    rw [comp_unpack' (hCT a ha) (hCT k hk),
      comp_unpack' (CFSG.KC.BfsPin.canonK_pcomp (hCT a ha) (hCT k hk)) (hCI a ha),
      pcomp_assoc' (hCT a ha) (hCT k hk) (hCI a ha)]
  have hcj : ∀ k < m, ∀ a < m,
      posOf (indexOf T) T (conjTab n T[a]! (T.map (invTab n))[a]! T[k]!) = fget (P k) a 8 :=
    fun k hk a ha => by rw [hconj k hk a ha, hpos _ (hP k hk a ha).1]
  set cj : Nat → Nat → Nat :=
    fun a k => posOf (indexOf T) T (conjTab n T[a]! (T.map (invTab n))[a]! T[k]!)
  have hcj' : ∀ k < m, ∀ a < m, cj a k = fget (P k) a 8 := hcj
  have H : ClassHyp m sizes cj (fun k => fget lab k 8) := by
    refine ⟨hm, fun k hk => ?_, fun l hl => ?_, fun k hk p hp => ⟨fun hpk => ?_, ?_⟩,
      fun l hl => ?_, hlab0⟩
    · rw [hz.1]
      exact (hwit k hk).1
    · have hl' : l < ns := by rw [← hz.1]; exact hl
      exact ⟨_, (hrep l hl').1, (hrep l hl').2⟩
    · have hpk' : fget lab p 8 = fget lab k 8 := hpk
      obtain ⟨hlk, hv, -⟩ := hwit k hk
      have hv' := (hwit p hp).2.1
      have hr := (hrep _ hlk).1
      obtain ⟨b, hb, e⟩ := hinv _ hv
      have hq := (hQ _ hv' b hb).2.1
      refine ⟨_, hq, ?_⟩
      rw [hcj' k hk _ hq, ← hPP k hk _ hv' b hb]
      have hkb : fget (P k) b 8 = fget rep (fget lab k 8) 8 := by
        have h1 := hPinv _ hr _ hv b hb e
        rwa [hPk k hk] at h1
      rw [hkb, ← hpk']
      exact hPk p hp
    · rintro ⟨a, ha, e⟩
      have e' : fget (P k) a 8 = p := (hcj' k hk a ha).symm.trans e
      have h1 := (hP k hk a ha).2.2
      rw [e'] at h1
      exact h1
    · have hl' : l < ns := by rw [← hz.1]; exact hl
      rw [hz.2 l hl', ← hcnt l hl', cntR_zero', length_filter_range_card]
      exact congrArg Finset.card (Finset.filter_congr fun k _ => (Iff.of_eq Nat.beq_eq).symm)
  have hck : ∀ k < m, fget lab k 8 < sizes.size := fun k hk => H.lt k hk
  obtain ⟨σ, hσ, hσi, hσ0, hRs, hlab, hreps, hwitn⟩ := classLoopN_spec H
  have hσs : ∀ l < sizes.size, ∃ l₀ < sizes.size, σ l₀ = l := by
    intro l hl
    let f : Fin sizes.size → Fin sizes.size := fun i => ⟨σ i, (hσ i i.2).1⟩
    have hf : Function.Injective f := fun i j e =>
      Fin.ext (hσi i i.2 j j.2 (congrArg Fin.val e))
    obtain ⟨i, hi⟩ := Finite.surjective_of_injective hf ⟨l, hl⟩
    exact ⟨i, i.2, congrArg Fin.val hi⟩
  have hCD : classData n T sizes = classLoopN m cj sizes := by
    rw [classData_eq_loop, hTs]
  rw [hCD]
  unfold classOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hTs]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨hinvs, ?_⟩, ?_⟩, hRs⟩, ?_⟩, ?_⟩, ?_⟩, hm⟩, ?_⟩, ?_⟩
  · exact CFSG.KS.BfsReplay.allBelow_iff.2 fun k hk => beq_iff_eq.2 (hpos k hk)
  · refine CFSG.KS.BfsReplay.allBelow_iff.2 fun k hk =>
      CFSG.KS.BfsReplay.allBelow_iff.2 fun a ha => ?_
    have hp := (hP k hk a ha).1
    simp only [Bool.and_eq_true, beq_iff_eq]
    rw [hconj k hk a ha, hpos _ hp, hlab _ hp, hlab k hk, (hP k hk a ha).2.2]
    exact ⟨hfound _ hp, rfl⟩
  · refine CFSG.KS.BfsReplay.allBelow_iff.2 fun l hl => ?_
    obtain ⟨l₀, hl₀, rfl⟩ := hσs l hl
    obtain ⟨h1, h2⟩ := hreps l₀ hl₀
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [hlab _ h1, h2]
    exact ⟨h1, rfl⟩
  · refine CFSG.KS.BfsReplay.allBelow_iff.2 fun k hk => ?_
    obtain ⟨hv, hcjk⟩ := hwitn k hk
    have hr1 := (hreps _ (hck k hk)).1
    have e : fget (P (classLoopN m cj sizes).reps[σ (fget lab k 8)]!)
        (classLoopN m cj sizes).wit[k]! 8 = k := (hcj' _ hr1 _ hv).symm.trans hcjk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [hlab k hk, hconj _ hr1 _ hv, e]
    exact ⟨⟨(hσ _ (hck k hk)).1, hv⟩, rfl⟩
  · refine CFSG.KS.BfsReplay.allBelow_iff.2 fun l hl => ?_
    obtain ⟨l₀, hl₀, rfl⟩ := hσs l hl
    rw [beq_iff_eq, (hσ l₀ hl₀).2, ← H.cnt l₀ hl₀]
    unfold countBelow
    rw [length_filter_range_card]
    refine congrArg Finset.card (Finset.filter_congr fun k hk => ?_)
    have hk' := Finset.mem_range.1 hk
    rw [beq_iff_eq, hlab k hk']
    exact ⟨fun e => hσi _ (hck k hk') _ hl₀ e, fun e => congrArg σ e⟩
  · rw [hTg 0 hm, h0]
    exact (idTab_unpack' hsz).symm
  · rw [hlab 0 hm, hlab0, hσ0]

theorem classOK_of_checks {n w m ns lab rep wit SZ : Nat} {CT CI Q P : Nat → Nat}
    {sizes : Array Nat} (hz : sizes.size = ns ∧ ∀ l < ns, sizes[l]! = fget SZ l 8)
    (hg : groupK n w m CT CI Q = true) (h : classK n w m CT CI P lab rep wit SZ ns = true) :
    classOK n (Array.ofFn (n := m) fun i => unpack n w (CT i.val))
      ((Array.ofFn (n := m) fun i => unpack n w (CT i.val)).map (invTab n))
      (classData n (Array.ofFn (n := m) fun i => unpack n w (CT i.val)) sizes) sizes = true :=
  classOK_of_tabs Array.size_ofFn (fun _ hi => pts_get hi) hz hg h

end Checks

end CFSG.KC.L34KSnd

end
