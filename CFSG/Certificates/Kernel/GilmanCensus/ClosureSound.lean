module

public import CFSG.Certificates.Kernel.GilmanCensus.CompsSound
import all Certificates.Data.Census
public import CFSG.Certificates.Kernel.GilmanCensus.LinAlgSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census

@[expose] def clInner (refl : Array (Array Nat)) (j i : Nat) (s : Nat × Array Nat) :
    Id (ForInStep (Nat × Array Nat)) :=
  if (!hasBit s.1 refl[i]![j]!) = true then
    pure (ForInStep.yield (s.1 ||| bit refl[i]![j]!, s.2.push refl[i]![j]!))
  else pure (ForInStep.yield (s.1, s.2))

@[expose] def clOuter (refl : Array (Array Nat)) (ids : Array Nat) (_ : Unit)
    (s : Nat × Array Nat) : Id (ForInStep (Nat × Array Nat)) :=
  if s.2.size > 0 then
    pure (ForInStep.yield (Id.run (forIn ids (s.1, s.2.pop) (clInner refl s.2.back!))))
  else pure (ForInStep.done (s.1, s.2))

@[expose] def clStep (refl : Array (Array Nat)) (j : Nat) (s : Nat × Array Nat) (i : Nat) :
    Nat × Array Nat :=
  if (!hasBit s.1 refl[i]![j]!) = true then (s.1 ||| bit refl[i]![j]!, s.2.push refl[i]![j]!)
  else (s.1, s.2)

theorem clInner_eq (refl : Array (Array Nat)) (j : Nat) (ids : Array Nat) (s : Nat × Array Nat) :
    Id.run (forIn ids s (clInner refl j)) = ids.toList.foldl (clStep refl j) s := by
  rw [← Array.forIn_toList]
  rw [forIn_yield (clStep refl j) _ (fun i s => by unfold clInner clStep; split <;> rfl)]
  rfl

theorem closureOf_run (dt : Data) (ids : Array Nat) :
    closureOf dt ids = (Id.run (forIn (m := Id) Lean.Loop.mk
      (ids.foldl (fun m i => m ||| bit i) 0, ids) (clOuter dt.refl ids))).1 := by
  unfold closureOf
  rfl

theorem hasBit_iff (m k : Nat) : hasBit m k = m.testBit k := by
  unfold hasBit
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  cases h : m / 2 ^ k % 2 == 1 <;> simp_all

theorem bit_eq (k : Nat) : bit k = 2 ^ k := by
  unfold bit
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem pc_le (m : Nat) : pc m ≤ 128 := by
  unfold pc
  exact Nat.le_trans List.countP_le_length (by simp)

theorem countP_eq_one (k : Nat) (hk : k < 128) :
    (List.range 128).countP (fun i => decide (k = i)) = 1 := by
  have h := List.count_range (a := k) (n := 128)
  rw [if_pos hk, List.count_eq_countP] at h
  rw [← h]
  apply List.countP_congr
  intro x _
  by_cases hx : x = k
  · subst hx
    simp
  · have : k ≠ x := fun h => hx h.symm
    simp [hx, this]

theorem pc_add_bit (seen k : Nat) (hk : k < 128) (hs : seen.testBit k = false) :
    pc (seen ||| bit k) = pc seen + 1 := by
  unfold pc
  rw [countP_or (fun i => seen.testBit i) (fun i => decide (k = i))
    (fun i => (seen ||| bit k).testBit i) (List.range 128)
    (fun x _ h => by
      have h2 := h.2
      simp only [decide_eq_true_eq] at h2
      subst h2
      rw [hs] at h
      simp at h)
    (fun x => by rw [bit_eq, Nat.testBit_or, Nat.testBit_two_pow])]
  rw [countP_eq_one k hk]

theorem testBit_or_bit (seen k : Nat) (hk : k < 128) (hs : seen < 2 ^ 128) :
    seen ||| bit k < 2 ^ 128 := by
  rw [bit_eq]
  exact Nat.or_lt_two_pow hs (Nat.pow_lt_pow_right (by decide) hk)

@[expose] def clStepK (j : Nat) (st : Nat × List Nat) (row : Nat) : Nat × List Nat :=
  let k := (row >>> (7 * j)) % 128
  if hasBitK st.1 k then st else (st.1 ||| bitK k, k :: st.2)

theorem cl_inner (refl : Array (Array Nat)) (P : Nat → Nat) (j : Nat) (hj : j < 128) :
    ∀ (l : List Nat), (∀ i ∈ l, (P i >>> (7 * j)) % 128 = refl[i]![j]!) →
    ∀ (s : Nat × Array Nat), s.1 < 2 ^ 128 → (∀ x ∈ s.2.toList, x < 128) →
    let r := l.foldl (clStep refl j) s
    let rk := (l.map P).foldl (clStepK j) (s.1, s.2.toList.reverse)
    rk = (r.1, r.2.toList.reverse) ∧ r.1 < 2 ^ 128 ∧ (∀ x ∈ r.2.toList, x < 128) ∧
      r.2.size + (128 - pc r.1) = s.2.size + (128 - pc s.1) := by
  intro l
  induction l with
  | nil =>
    intro _ s hs ht
    exact ⟨rfl, hs, ht, rfl⟩
  | cons i l ih =>
    intro hP s hs ht
    simp only [List.foldl_cons, List.map_cons]
    have hk := hP i (by simp)
    have hklt : refl[i]![j]! < 128 := by rw [← hk]; exact Nat.mod_lt _ (by decide)
    have hstep : clStepK j (s.1, s.2.toList.reverse) (P i) =
        ((clStep refl j s i).1, (clStep refl j s i).2.toList.reverse) := by
      unfold clStepK clStep
      dsimp only
      rw [hk]
      have e : hasBitK s.1 refl[i]![j]! = hasBit s.1 refl[i]![j]! := rfl
      rw [e]
      cases hb : hasBit s.1 refl[i]![j]!
      · simp [bitK, bit]
      · simp
    have hs1 : (clStep refl j s i).1 < 2 ^ 128 := by
      unfold clStep
      split
      · exact testBit_or_bit _ _ hklt hs
      · exact hs
    have ht1 : ∀ x ∈ (clStep refl j s i).2.toList, x < 128 := by
      unfold clStep
      split
      · intro x hx
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx
        · exact ht x hx
        · rw [hx]
          exact hklt
      · exact ht
    have hc1 : (clStep refl j s i).2.size + (128 - pc (clStep refl j s i).1) =
        s.2.size + (128 - pc s.1) := by
      unfold clStep
      split
      · rename_i hb
        have hb' : s.1.testBit refl[i]![j]! = false := by
          rw [← hasBit_iff]
          simpa using hb
        have := pc_add_bit s.1 _ hklt hb'
        have h2 := pc_le (s.1 ||| bit refl[i]![j]!)
        simp only [Array.size_push]
        omega
      · rfl
    obtain ⟨r1, r2, r3, r4⟩ := ih (fun i' hi' => hP i' (by simp [hi'])) _ hs1 ht1
    rw [hstep]
    exact ⟨r1, r2, r3, r4.trans hc1⟩

theorem reverse_pop (a : Array Nat) (h : 0 < a.size) :
    a.toList.reverse = a.back! :: a.pop.toList.reverse := by
  have e : a.toList = a.pop.toList ++ [a.back!] := by
    conv => lhs; rw [Array.eq_push_pop_back!_of_size_ne_zero (by omega : a.size ≠ 0)]
    rw [Array.toList_push]
  rw [e]
  simp

theorem back_lt (a : Array Nat) (h : 0 < a.size) (ht : ∀ x ∈ a.toList, x < 128) : a.back! < 128 := by
  apply ht
  have := reverse_pop a h
  have hm : a.back! ∈ a.toList.reverse := by rw [this]; simp
  simpa using hm

theorem cl_outer (refl : Array (Array Nat)) (P : Nat → Nat) (ids : Array Nat)
    (hP : ∀ i ∈ ids.toList, ∀ j < 128, (P i >>> (7 * j)) % 128 = refl[i]![j]!) :
    ∀ (f : Nat) (s : Nat × Array Nat), s.1 < 2 ^ 128 → (∀ x ∈ s.2.toList, x < 128) →
      s.2.size + (128 - pc s.1) ≤ f →
      (Id.run (forIn (m := Id) Lean.Loop.mk s (clOuter refl ids))).1 =
        clGo (ids.toList.map P) f s.1 s.2.toList.reverse := by
  intro f
  induction f with
  | zero =>
    intro s hs ht hf
    have h0 : s.2.size = 0 := by omega
    rw [loop_unfold]
    have : ¬s.2.size > 0 := by omega
    simp only [clOuter, this, ↓reduceIte]
    rfl
  | succ f ih =>
    intro s hs ht hf
    by_cases h0 : s.2.size > 0
    · rw [loop_unfold]
      simp only [clOuter, h0, ↓reduceIte]
      rw [reverse_pop s.2 h0, clInner_eq]
      have hj := back_lt s.2 h0 ht
      have hpop : ∀ x ∈ s.2.pop.toList, x < 128 := by
        intro x hx
        rw [Array.toList_pop] at hx
        exact ht x (List.dropLast_subset _ hx)
      obtain ⟨r1, r2, r3, r4⟩ := cl_inner refl P s.2.back! hj ids.toList
        (fun i hi => hP i hi _ hj) (s.1, s.2.pop) hs hpop
      dsimp only at r1 r2 r3 r4
      change (Id.run (forIn (m := Id) Lean.Loop.mk (ids.toList.foldl (clStep refl s.2.back!)
        (s.1, s.2.pop)) (clOuter refl ids))).1 = _
      rw [ih _ r2 r3 (by rw [r4, Array.size_pop]; omega)]
      change _ = clGo (ids.toList.map P) f
        ((ids.toList.map P).foldl (clStepK s.2.back!) (s.1, s.2.pop.toList.reverse)).1
        ((ids.toList.map P).foldl (clStepK s.2.back!) (s.1, s.2.pop.toList.reverse)).2
      rw [r1]
    · have h00 : s.2.size = 0 := by omega
      rw [loop_unfold]
      simp only [clOuter, h0, ↓reduceIte]
      have : s.2.toList = [] := by
        rw [← List.length_eq_zero_iff, Array.length_toList, h00]
      rw [this]
      rfl

theorem seen0_lt : ∀ (l : List Nat) (acc : Nat), acc < 2 ^ 128 → (∀ i ∈ l, i < 128) →
    l.foldl (fun m i => m ||| bit i) acc < 2 ^ 128
  | [], _, h, _ => h
  | i :: l, acc, h, hl => by
    rw [List.foldl_cons]
    exact seen0_lt l _ (testBit_or_bit acc i (hl i (by simp)) h) (fun j hj => hl j (by simp [hj]))

theorem closure_eq (dt : Data) (P : Nat → Nat) (ids : Array Nat)
    (hP : ∀ i ∈ ids.toList, ∀ j < 128, (P i >>> (7 * j)) % 128 = dt.refl[i]![j]!)
    (hids : ∀ i ∈ ids.toList, i < 128) (hn : ids.size ≤ 128) :
    closureOf dt ids = clGo (ids.toList.map P) 256
      (ids.toList.foldl (fun m i => m ||| bitK i) 0) ids.toList.reverse := by
  have hpc := pc_le (ids.foldl (fun m i => m ||| bit i) 0)
  have hs0 : ids.foldl (fun m i => m ||| bit i) 0 < 2 ^ 128 := by
    rw [← Array.foldl_toList]
    exact seen0_lt _ 0 (by decide) hids
  rw [closureOf_run, cl_outer dt.refl P ids hP 256 _ hs0 hids (by dsimp only; omega)]
  dsimp only
  rw [← Array.foldl_toList]
  rfl

end Certificates.GilmanCensusK

end
