module

public import CFSG.Certificates.Kernel.Spor.KeyBfsGen

public section

namespace CFSG.KS.HashBfs

open CFSG.KS.KeyBfsG

variable {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [Inhabited α]

@[expose] def hashBfs (root : α) (st : Nat → α → α) (k cap : Nat) : Array Nat × Array Nat :=
  Id.run do
  let mut nodes : Array α := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Std.HashSet α := (∅ : Std.HashSet α).insert root
  let mut i := 0
  for _ in [0:cap] do
    if i < nodes.size then
      let t := nodes[i]!
      for l in [0:k] do
        let t2 := st l t
        if !seen.contains t2 then
          seen := seen.insert t2
          nodes := nodes.push t2
          par := par.push i
          lab := lab.push l
      i := i + 1
  return (par, lab)

abbrev HSt (α : Type) [BEq α] [Hashable α] :=
  Array α × Array Nat × Array Nat × Std.HashSet α × Nat

def innerH (st : Nat → α → α) (r : α) (h l : Nat)
    (s : Array α × Array Nat × Array Nat × Std.HashSet α) :
    Id (ForInStep (Array α × Array Nat × Array Nat × Std.HashSet α)) :=
  if (!s.2.2.2.contains (st l r)) = true then
    pure (ForInStep.yield (s.1.push (st l r), s.2.1.push h, s.2.2.1.push l,
      s.2.2.2.insert (st l r)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

def outerH (st : Nat → α → α) (k : Nat) (_x : Nat) (s : HSt α) : Id (ForInStep (HSt α)) :=
  if s.2.2.2.2 < s.1.size then
    pure (ForInStep.yield (let s1 := Id.run (forIn (List.range' 0 k)
      (s.1, s.2.1, s.2.2.1, s.2.2.2.1) (innerH st s.1[s.2.2.2.2]! s.2.2.2.2));
      (s1.1, s1.2.1, s1.2.2.1, s1.2.2.2, s.2.2.2.2 + 1)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

theorem hashBfs_eq_loop (root : α) (st : Nat → α → α) (k cap : Nat) :
    hashBfs root st k cap =
      ((Id.run (forIn (List.range' 0 cap) ((#[root], #[0], #[0],
        (∅ : Std.HashSet α).insert root, 0) : HSt α) (outerH st k))).2.1,
      (Id.run (forIn (List.range' 0 cap) ((#[root], #[0], #[0],
        (∅ : Std.HashSet α).insert root, 0) : HSt α) (outerH st k))).2.2.1) := by
  unfold hashBfs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem forIn_rel {β γ : Type} (Rl : Nat → β → γ → Prop)
    (f : Nat → β → Id (ForInStep β)) (g : Nat → γ → Id (ForInStep γ))
    (h : ∀ x b c, Rl x b c → ∃ b' c', f x b = pure (ForInStep.yield b') ∧
      g x c = pure (ForInStep.yield c') ∧ Rl (x + 1) b' c') :
    ∀ (n s : Nat) (b : β) (c : γ), Rl s b c →
      Rl (s + n) (Id.run (forIn (List.range' s n) b f)) (Id.run (forIn (List.range' s n) c g)) := by
  intro n
  induction n with
  | zero => intro s b c h0; exact h0
  | succ n ih =>
    intro s b c h0
    obtain ⟨b', c', hf, hg, h1⟩ := h s b c h0
    rw [List.range'_succ, List.forIn_cons, List.forIn_cons, hf, hg]
    have := ih (s + 1) b' c' h1
    rw [show s + (n + 1) = s + 1 + n by omega]
    exact this

def SeenRel (κ : α → Nat) (A : Std.HashSet α) (K : Std.HashSet Nat) : Prop :=
  ∀ y, A.contains y = K.contains (κ y)

theorem seenRel_insert {κ : α → Nat} (hκ : Function.Injective κ) {A : Std.HashSet α}
    {K : Std.HashSet Nat} (h : SeenRel κ A K) (x : α) :
    SeenRel κ (A.insert x) (K.insert (κ x)) := by
  intro y
  rw [Std.HashSet.contains_insert, Std.HashSet.contains_insert, h y]
  congr 1
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  exact ⟨fun e => e ▸ rfl, fun e => hκ e⟩

def HRel (κ : α → Nat) (h : Nat) (s : HSt α) (g : GSt α) : Prop :=
  g.1 = s.1 ∧ g.2.1 = s.2.1 ∧ g.2.2.1 = s.2.2.1 ∧ SeenRel κ s.2.2.2.1 g.2.2.2 ∧
    ((s.2.2.2.2 = h ∧ h ≤ s.1.size) ∨ (s.2.2.2.2 = s.1.size ∧ s.1.size ≤ h))

def IRel (κ : α → Nat) (i : Nat) (r : α) (b : Array α × Array Nat × Array Nat × Std.HashSet α)
    (c : GSt α) : Prop :=
  c.1 = b.1 ∧ c.2.1 = b.2.1 ∧ c.2.2.1 = b.2.2.1 ∧ SeenRel κ b.2.2.2 c.2.2.2 ∧ i < b.1.size ∧
    b.1[i]! = r

theorem iRel_step {κ : α → Nat} (hκ : Function.Injective κ) (st : Nat → α → α) (i : Nat)
    (r : α) : ∀ (l : Nat) b c, IRel κ i r b c →
      ∃ b' c', innerH st r i l b = pure (ForInStep.yield b') ∧
        innerG κ st i l c = pure (ForInStep.yield c') ∧ IRel κ i r b' c' := by
  rintro l ⟨B1, B2, B3, B4⟩ ⟨C1, C2, C3, C4⟩ ⟨e1, e2, e3, hs, hi, hr⟩
  dsimp only at e1 e2 e3 hs hi hr
  subst e1 e2 e3
  have hc : C1[i]! = r := hr
  by_cases hin : B4.contains (st l r) = true
  · have hin' : C4.contains (κ (st l r)) = true := by rw [← hs]; exact hin
    refine ⟨(C1, C2, C3, B4), (C1, C2, C3, C4), ?_, ?_, ⟨rfl, rfl, rfl, hs, hi, hr⟩⟩
    · simp only [innerH, hin, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · simp only [innerG, hc, hin', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · have hnc := Bool.eq_false_iff.2 hin
    have hnc' : C4.contains (κ (st l r)) = false := by rw [← hs]; exact hnc
    refine ⟨(C1.push (st l r), C2.push i, C3.push l, B4.insert (st l r)),
      (C1.push (st l r), C2.push i, C3.push l, C4.insert (κ (st l r))), ?_, ?_,
      ⟨rfl, rfl, rfl, seenRel_insert hκ hs _, ?_, ?_⟩⟩
    · simp only [innerH, hnc, Bool.not_false, ↓reduceIte]
    · simp only [innerG, hc, hnc', Bool.not_false, ↓reduceIte]
    · simp only [Array.size_push]
      omega
    · simp only
      rw [CFSG.KS.KeyBfs.push_lt hi]
      exact hr

theorem hRel_step {κ : α → Nat} (hκ : Function.Injective κ) (st : Nat → α → α) (k : Nat) :
    ∀ x b c, HRel κ x b c → ∃ b' c', outerH st k x b = pure (ForInStep.yield b') ∧
      outerG κ st k x c = pure (ForInStep.yield c') ∧ HRel κ (x + 1) b' c' := by
  rintro x ⟨rows, par, lab, seen, i⟩ ⟨C1, C2, C3, C4⟩ ⟨e1, e2, e3, hs, hi⟩
  dsimp only at e1 e2 e3 hs hi
  subst e1 e2 e3
  by_cases hlt : i < C1.size
  · have hx : i = x := by omega
    subst hx
    obtain ⟨f1, f2, f3, fs, fsz, -⟩ := forIn_rel (fun _ => IRel κ i C1[i]!)
      (innerH st C1[i]! i) (innerG κ st i) (iRel_step hκ st i C1[i]!) k 0
      (C1, C2, C3, seen) (C1, C2, C3, C4) ⟨rfl, rfl, rfl, hs, hlt, rfl⟩
    refine ⟨_, _, by simp only [outerH, hlt, ↓reduceIte]; rfl,
      by simp only [outerG, hlt, ↓reduceIte]; rfl, ⟨f1, f2, f3, fs, Or.inl ⟨rfl, ?_⟩⟩⟩
    exact fsz
  · have hx : ¬ x < C1.size := by omega
    refine ⟨(C1, C2, C3, seen, i), (C1, C2, C3, C4),
      by simp only [outerH, hlt, ↓reduceIte],
      by simp only [outerG, hx, ↓reduceIte], ⟨rfl, rfl, rfl, hs, Or.inr ⟨by dsimp only; omega,
        by dsimp only; omega⟩⟩⟩

theorem hashBfs_eq_keyBfsG {κ : α → Nat} (hκ : Function.Injective κ) (root : α)
    (st : Nat → α → α) (k cap : Nat) :
    hashBfs root st k cap =
      ((keyBfsG κ st k root (κ root) cap).2.1, (keyBfsG κ st k root (κ root) cap).2.2) := by
  rw [hashBfs_eq_loop, keyBfsG_eq]
  have h0 : HRel κ 0 ((#[root], #[0], #[0], (∅ : Std.HashSet α).insert root, 0) : HSt α)
      (initG root (κ root)) := by
    refine ⟨rfl, rfl, rfl, ?_, Or.inl ⟨rfl, by simp⟩⟩
    intro y
    change ((∅ : Std.HashSet α).insert root).contains y =
      ((∅ : Std.HashSet Nat).insert (κ root)).contains (κ y)
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_insert, Std.HashSet.contains_empty,
      Std.HashSet.contains_empty, Bool.or_false, Bool.or_false]
    apply Bool.eq_iff_iff.2
    simp only [beq_iff_eq]
    exact ⟨fun e => e ▸ rfl, fun e => hκ e⟩
  obtain ⟨-, e2, e3, -⟩ := forIn_rel (HRel κ) (outerH st k) (outerG κ st k) (hRel_step hκ st k)
    cap 0 _ _ h0
  rw [e2, e3]

theorem hashBfs_rec {κ : α → Nat} (hκ : Function.Injective κ) {st : Nat → α → α} {k : Nat}
    {root : α} {cnt Ec : Nat} {T : Nat → α} {P L POS : Nat → Nat}
    (R : GRec κ st k root (κ root) cnt Ec T P L POS) {cap : Nat} (hcap : P (cnt - 1) < cap)
    (hE : k * cnt ≤ Ec) :
    hashBfs root st k cap =
      (((List.range cnt).map P).toArray, ((List.range cnt).map L).toArray) := by
  obtain ⟨-, hget, hsz, hps, hls⟩ := keyBfsG_rec R hcap
  have hsz' := hsz hE
  rw [hashBfs_eq_keyBfsG hκ]
  congr 1
  · apply Array.ext
    · rw [hps, hsz', List.size_toArray, List.length_map, List.length_range]
    · intro j h1 h2
      rw [← getElem!_pos _ j h1]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      exact (hget j (by rw [hps, hsz'] at h1; exact h1)).2.1
  · apply Array.ext
    · rw [hls, hsz', List.size_toArray, List.length_map, List.length_range]
    · intro j h1 h2
      rw [← getElem!_pos _ j h1]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      exact (hget j (by rw [hls, hsz'] at h1; exact h1)).2.2

end CFSG.KS.HashBfs

end
