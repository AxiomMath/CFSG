module

import all Certificates.Data.Census
public import CFSG.Certificates.Kernel.GilmanCensus.DetSound
public import CFSG.Certificates.Kernel.GilmanCensus.ExtSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census

@[expose] def cmat (dt : Data) (V : Array (Nat × Int)) : Array (Array Int) :=
  Array.ofFn (n := V.size) fun a => Array.ofFn (n := V.size) fun b =>
    2 * V[a.val]!.2 * V[b.val]!.2 * dt.G[V[a.val]!.1]![V[b.val]!.1]! /
      dt.G[V[b.val]!.1]![V[b.val]!.1]!

@[expose] def dgInner (C : Array (Array Int)) (i j : Nat) (s : Nat × Array Nat) :
    Id (ForInStep (Nat × Array Nat)) :=
  if (!hasBit s.1 j && i != j && C[i]![j]! != 0) = true then
    pure (ForInStep.yield (s.1 ||| bit j, s.2.push j))
  else pure (ForInStep.yield (s.1, s.2))

@[expose] def dgOuter (C : Array (Array Int)) (m : Nat) (_ : Unit) (s : Nat × Array Nat) :
    Id (ForInStep (Nat × Array Nat)) :=
  if s.2.size > 0 then
    pure (ForInStep.yield (Id.run (forIn [0:m] (s.1, s.2.pop) (dgInner C s.2.back!))))
  else pure (ForInStep.done (s.1, s.2))

@[expose] def dgLoop (C : Array (Array Int)) (m : Nat) : Nat :=
  (Id.run (forIn (m := Id) Lean.Loop.mk ((1 : Nat), #[0]) (dgOuter C m))).1

@[expose] def dgBody (C : Array (Array Int)) (m : Nat) : Option (Array (Array Int) × Int) :=
  Id.run do
  for i in [0:m] do
    for j in [0:m] do
      if i != j && C[i]![j]! > 0 then return none
  let dd := detInt C
  if dd ≤ 0 then return none
  let seen := dgLoop C m
  if popc seen != m then return none
  let mut att := 0
  for j in [0:m-1] do
    if C[m-1]![j]! != 0 then att := att + 1
  if att != 1 then return none
  return some (C, dd)

theorem diagram_run (dt : Data) (V : Array (Nat × Int)) : diagram dt V = dgBody (cmat dt V) V.size := by
  unfold diagram dgBody cmat dgLoop dgOuter dgInner
  rfl

theorem early_loop {α : Type} (x : α) (P : Nat → Bool) (f : Nat → Option α × Unit → Id (ForInStep (Option α × Unit)))
    (hf : ∀ j s, f j s = if P j = true then ForInStep.done (some x, ()) else ForInStep.yield (none, ())) :
    ∀ l : List Nat, forIn (m := Id) l (none, ()) f = if l.any P = true then (some x, ()) else (none, ())
  | [] => rfl
  | j :: l => by
    rw [List.forIn_cons, hf j, List.any_cons]
    by_cases hp : P j = true
    · simp [hp]
      rfl
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      exact early_loop x P f hf l

theorem foldl_count (p : Nat → Bool) : ∀ (l : List Nat) (a : Nat),
    l.foldl (fun a j => if p j = true then a + 1 else a) a = a + (l.filter p).length
  | [], a => rfl
  | j :: l, a => by
    rw [List.foldl_cons, foldl_count p l, List.filter_cons]
    by_cases hp : p j = true
    · simp [hp]
      omega
    · simp [hp]

theorem dgBody_struct (C : Array (Array Int)) (m : Nat) :
    dgBody C m =
      if (List.range m).any (fun i => (List.range m).any fun j => i != j && decide (C[i]![j]! > 0))
      then none else if detInt C ≤ 0 then none else if popc (dgLoop C m) != m then none else
      if ((List.range (m - 1)).filter fun j => C[m - 1]![j]! != 0).length != 1 then none
      else some (C, detInt C) := by
  unfold dgBody
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [early_loop none (fun i => (List.range m).any fun j => i != j && decide (C[i]![j]! > 0)) _
    ?_ (List.range' 0 m)]
  · rw [← List.range_eq_range']
    by_cases hn : ((List.range m).any fun i => (List.range m).any fun j =>
        i != j && decide (C[i]![j]! > 0)) = true
    · simp only [hn, ↓reduceIte]
      rfl
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]
      change (if detInt C ≤ 0 then pure none else _ : Id _).run = _
      split
      · rfl
      split
      · rfl
      rw [forIn_yieldG (fun a j => if (C[m - 1]![j]! != 0) = true then a + 1 else a) _
        (fun j a => by split <;> rfl), foldl_count, Nat.zero_add, ← List.range_eq_range']
      rfl
  · intro i s
    rw [early_loop none (fun j => i != j && decide (C[i]![j]! > 0)) _
      (fun j s => by split <;> rfl) (List.range' 0 m), ← List.range_eq_range']
    split <;> rfl

theorem pc_le_of_lt (s k : Nat) (hs : s < 2 ^ k) (hk : k ≤ 128) : pc s ≤ k := by
  unfold pc
  have e : (128 : Nat) = k + (128 - k) := by omega
  rw [e, List.range_add, List.countP_append]
  have h0 : (List.map (fun x => k + x) (List.range (128 - k))).countP (fun i => s.testBit i) = 0 := by
    rw [List.countP_eq_zero]
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨b, _, rfl⟩ := ha
    have : s < 2 ^ (k + b) := Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) (by omega))
    simp [Nat.testBit_lt_two_pow this]
  rw [h0, Nat.add_zero]
  exact Nat.le_trans List.countP_le_length (by simp)

@[expose] def dgStep (C : Array (Array Int)) (i : Nat) (s : Nat × Array Nat) (j : Nat) : Nat × Array Nat :=
  if (!hasBit s.1 j && i != j && C[i]![j]! != 0) = true then (s.1 ||| bit j, s.2.push j) else (s.1, s.2)

@[expose] def dgStepK (C : List (List Int)) (i : Nat) (st : Nat × List Nat) (j : Nat) : Nat × List Nat :=
  if !hasBitK st.1 j && i != j && (C.getD i []).getD j 0 != 0 then (st.1 ||| bitK j, j :: st.2) else st

theorem dg_inner (C : Array (Array Int)) (i k : Nat) (hk : k ≤ 128) :
    ∀ (l : List Nat), (∀ j ∈ l, j < k) →
    ∀ (s : Nat × Array Nat), s.1 < 2 ^ k → (∀ x ∈ s.2.toList, x < k) →
    let r := l.foldl (dgStep C i) s
    let rk := l.foldl (dgStepK (LLI C) i) (s.1, s.2.toList.reverse)
    rk = (r.1, r.2.toList.reverse) ∧ r.1 < 2 ^ k ∧ (∀ x ∈ r.2.toList, x < k) ∧
      r.2.size + (k - pc r.1) = s.2.size + (k - pc s.1) := by
  intro l
  induction l with
  | nil =>
    intro _ s hs ht
    exact ⟨rfl, hs, ht, rfl⟩
  | cons j l ih =>
    intro hl s hs ht
    simp only [List.foldl_cons]
    have hj := hl j (by simp)
    have hstep : dgStepK (LLI C) i (s.1, s.2.toList.reverse) j =
        ((dgStep C i s j).1, (dgStep C i s j).2.toList.reverse) := by
      unfold dgStepK dgStep
      dsimp only
      rw [← getEntI]
      have e : hasBitK s.1 j = hasBit s.1 j := rfl
      rw [e]
      split
      · simp [bitK, bit]
      · simp
    have hb2 : 2 ^ j < 2 ^ k := Nat.pow_lt_pow_right (by decide) hj
    have hs1 : (dgStep C i s j).1 < 2 ^ k := by
      unfold dgStep
      split
      · rw [bit_eq]
        exact Nat.or_lt_two_pow hs hb2
      · exact hs
    have ht1 : ∀ x ∈ (dgStep C i s j).2.toList, x < k := by
      unfold dgStep
      split
      · intro x hx
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx
        · exact ht x hx
        · rw [hx]
          exact hj
      · exact ht
    have hc1 : (dgStep C i s j).2.size + (k - pc (dgStep C i s j).1) =
        s.2.size + (k - pc s.1) := by
      unfold dgStep
      split
      · rename_i hb
        have hb' : s.1.testBit j = false := by
          rw [← hasBit_iff]
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
          exact hb.1.1
        have := pc_add_bit s.1 j (by omega) hb'
        have h2 := pc_le_of_lt (s.1 ||| bit j) k (by rw [bit_eq]; exact Nat.or_lt_two_pow hs hb2) hk
        simp only [Array.size_push]
        omega
      · rfl
    obtain ⟨r1, r2, r3, r4⟩ := ih (fun j' hj' => hl j' (by simp [hj'])) _ hs1 ht1
    rw [hstep]
    exact ⟨r1, r2, r3, r4.trans hc1⟩

theorem dgInner_eq (C : Array (Array Int)) (i m : Nat) (s : Nat × Array Nat) :
    Id.run (forIn [0:m] s (dgInner C i)) = (List.range m).foldl (dgStep C i) s := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yieldG (dgStep C i) _ (fun j s => by unfold dgInner dgStep; split <;> rfl),
    ← List.range_eq_range']
  rfl

theorem dg_outer (C : Array (Array Int)) (m k : Nat) (hm : m ≤ k) (hk : k ≤ 128) :
    ∀ (f : Nat) (s : Nat × Array Nat), s.1 < 2 ^ k → (∀ x ∈ s.2.toList, x < k) →
      s.2.size + (k - pc s.1) ≤ f →
      (Id.run (forIn (m := Id) Lean.Loop.mk s (dgOuter C m))).1 =
        dgGo (LLI C) m f s.1 s.2.toList.reverse := by
  intro f
  induction f with
  | zero =>
    intro s hs ht hf
    rw [loop_unfold]
    have : ¬s.2.size > 0 := by omega
    simp only [dgOuter, this, ↓reduceIte]
    rfl
  | succ f ih =>
    intro s hs ht hf
    by_cases h0 : s.2.size > 0
    · rw [loop_unfold]
      simp only [dgOuter, h0, ↓reduceIte]
      rw [reverse_pop s.2 h0, dgInner_eq]
      have hpop : ∀ x ∈ s.2.pop.toList, x < k := by
        intro x hx
        rw [Array.toList_pop] at hx
        exact ht x (List.dropLast_subset _ hx)
      obtain ⟨r1, r2, r3, r4⟩ := dg_inner C s.2.back! k hk (List.range m)
        (fun j hj => by simp at hj; omega) (s.1, s.2.pop) hs hpop
      dsimp only at r1 r2 r3 r4
      change (Id.run (forIn (m := Id) Lean.Loop.mk ((List.range m).foldl (dgStep C s.2.back!)
        (s.1, s.2.pop)) (dgOuter C m))).1 = _
      rw [ih _ r2 r3 (by rw [r4, Array.size_pop]; omega)]
      change _ = dgGo (LLI C) m f
        ((List.range m).foldl (dgStepK (LLI C) s.2.back!) (s.1, s.2.pop.toList.reverse)).1
        ((List.range m).foldl (dgStepK (LLI C) s.2.back!) (s.1, s.2.pop.toList.reverse)).2
      rw [r1]
    · have h00 : s.2.size = 0 := by omega
      rw [loop_unfold]
      simp only [dgOuter, h0, ↓reduceIte]
      have : s.2.toList = [] := by
        rw [← List.length_eq_zero_iff, Array.length_toList, h00]
      rw [this]
      rfl

theorem pc_one : pc 1 = 1 := by
  have := pc_add_bit 0 0 (by decide) (by decide)
  have e : (0 ||| bit 0) = 1 := by decide
  rw [e] at this
  rw [this]
  decide

theorem dgLoop_eq (C : Array (Array Int)) (m : Nat) (hm : m ≤ 127) :
    dgLoop C m = dgGo (LLI C) m (m + 1) 1 [0] := by
  unfold dgLoop
  have hk : max m 1 ≤ 128 := by omega
  rw [dg_outer C m (max m 1) (by omega) hk (m + 1) (1, #[0])
    (by
      have : 2 ^ 1 ≤ 2 ^ max m 1 := Nat.pow_le_pow_right (by decide) (by omega)
      simp only
      omega)
    (by simp; omega) (by simp only [List.size_toArray, List.length_singleton]; rw [pc_one]; omega)]
  rfl

theorem foldl_dgStepK_lt (C : List (List Int)) (i k : Nat) : ∀ (l : List Nat) (st : Nat × List Nat),
    (∀ j ∈ l, j < k) → st.1 < 2 ^ k → (l.foldl (dgStepK C i) st).1 < 2 ^ k
  | [], _, _, hs => hs
  | j :: l, st, hl, hs => by
    rw [List.foldl_cons]
    apply foldl_dgStepK_lt C i k l _ (fun j' hj' => hl j' (by simp [hj']))
    unfold dgStepK
    split
    · rw [bitK, Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.or_lt_two_pow hs (Nat.pow_lt_pow_right (by decide) (hl j (by simp)))
    · exact hs

theorem dgGo_lt (C : List (List Int)) (m k : Nat) (hm : m ≤ k) :
    ∀ (f seen : Nat) (todo : List Nat), seen < 2 ^ k → dgGo C m f seen todo < 2 ^ k
  | 0, _, _, hs => by simpa [dgGo] using hs
  | _ + 1, _, [], hs => by simpa [dgGo] using hs
  | f + 1, seen, i :: todo, hs => by
    simp only [dgGo]
    exact dgGo_lt C m k hm f _ _ (foldl_dgStepK_lt C i k (List.range m) (seen, todo)
      (fun j hj => by simp at hj; omega) hs)

theorem cmat_eq {dt : Data} {dk : DK} (h : Rel dt dk) (V : List (Nat × Int))
    (hV : ∀ p ∈ V, p.1 < dk.N) :
    LLI (cmat dt V.toArray) = V.map fun a => V.map fun b =>
      2 * a.2 * b.2 * gI dk a.1 b.1 / gI dk b.1 b.1 := by
  unfold cmat LLI
  rw [Array.toList_ofFn]
  apply List.ext_getElem
  · simp
  · intro a h1 h2
    simp only [List.getElem_map, List.getElem_ofFn, Array.toList_ofFn]
    apply List.ext_getElem
    · simp
    · intro b h3 h4
      simp only [List.getElem_map, List.getElem_ofFn, List.length_ofFn] at h3 ⊢
      have ha : a < V.length := by simpa using h1
      have hb : b < V.length := by simpa using h3
      have e1 : V.toArray[a]! = V[a] := by
        rw [getElem!_pos V.toArray a (by simpa using ha)]
        simp
      have e2 : V.toArray[b]! = V[b] := by
        rw [getElem!_pos V.toArray b (by simpa using hb)]
        simp
      have na := hV _ (List.getElem_mem ha)
      have nb := hV _ (List.getElem_mem hb)
      rw [e1, e2, h.G _ _ na nb, h.G _ _ nb nb]

theorem diagram_eq {dt : Data} {dk : DK} (h : Rel dt dk) (V : List (Nat × Int))
    (hV : ∀ p ∈ V, p.1 < dk.N) (hl : V.length ≤ 127) :
    (diagram dt V.toArray).map (fun p => (LLI p.1, p.2)) = diagramK dk V := by
  rw [diagram_run, dgBody_struct, dgLoop_eq _ _ (by simpa using hl)]
  have hC := cmat_eq h V hV
  have hd : detInt (cmat dt V.toArray) = detIntK (LLI (cmat dt V.toArray)) := detInt_eq _
  have hp : popc (dgGo (LLI (cmat dt V.toArray)) V.length (V.length + 1) 1 [0]) =
      popcK (dgGo (LLI (cmat dt V.toArray)) V.length (V.length + 1) 1 [0]) :=
    popc_eq _ (dgGo_lt _ V.length 128 (by omega) _ _ _ (by decide))
  simp only [List.size_toArray, hd, hp, getEntI]
  rw [hC]
  unfold diagramK
  dsimp only
  split
  · rfl
  split
  · rfl
  split
  · rfl
  split
  · rfl
  rw [Option.map_some, hC]

end Certificates.GilmanCensusK

end
