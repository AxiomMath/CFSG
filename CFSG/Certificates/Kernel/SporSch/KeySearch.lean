
module

public import CFSG.Sporadic.Schreier.Co3OrbitTCheckInputs
import all CFSG.Sporadic.Schreier.Co3OrbitTCheckInputs

public section

namespace CFSG.KS.SporSch.KeySearch

open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native

instance : LawfulBEq Co3Key where
  eq_of_beq {a b} h := by
    cases a
    cases b
    unfold BEq.beq instBEqCo3Key instBEqCo3Key.beq at h
    simp_all
  rfl {a} := by
    cases a
    unfold BEq.beq instBEqCo3Key instBEqCo3Key.beq
    simp

instance : LawfulHashable Co3Key where
  hash_eq {a b} h := by rw [eq_of_beq h]

theorem key_beq (a b : Nat) : ((⟨a⟩ : Co3Key) == ⟨b⟩) = decide (a = b) := by
  by_cases h : a = b
  · subst h
    simp
  · rw [decide_eq_false h]
    exact beq_false_of_ne fun e => h (Co3Key.mk.inj e)

theorem forIn_range'_ind {β : Type} (n s : Nat) (init : β) (f : Nat → β → Id (ForInStep β))
    (P : Nat → β → Prop)
    (h : ∀ j < n, ∀ b, P j b → ∃ b', f (s + j) b = pure (ForInStep.yield b') ∧ P (j + 1) b')
    (h0 : P 0 init) : P n (Id.run (forIn (List.range' s n) init f)) := by
  induction n generalizing s init P with
  | zero => simpa using h0
  | succ n ih =>
    obtain ⟨b', hb, hP⟩ := h 0 (by omega) init h0
    rw [Nat.add_zero] at hb
    rw [List.range'_succ, List.forIn_cons, hb]
    have := ih (s + 1) b' (fun j b => P (j + 1) b) (fun j hj b hbj => by
      obtain ⟨b'', e, p⟩ := h (j + 1) (by omega) b hbj
      exact ⟨b'', by rw [show s + 1 + j = s + (j + 1) by omega]; exact e, p⟩) hP
    simpa using this

@[expose] def Good (n : Nat) (l : List Nat) : Prop := l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < n

@[expose] def PermA (n : Nat) (g : Array Nat) : Prop :=
  (∀ x < n, g[x]! < n) ∧ ∀ x < n, ∀ y < n, g[x]! = g[y]! → x = y

theorem testBit_foldl (l : List Nat) (a q : Nat) :
    (l.foldl (fun acc p => acc ||| (1 <<< p)) a).testBit q = (a.testBit q || decide (q ∈ l)) := by
  induction l generalizing a with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : q = p
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem mem_of_setKey {a b : List Nat} (h : setKey a = setKey b) (q : Nat) : q ∈ a ↔ q ∈ b := by
  have e := congrArg (fun x => x.testBit q) h
  simp only [setKey, testBit_foldl, Nat.zero_testBit, Bool.false_or, decide_eq_decide] at e
  exact e

theorem eq_of_setKey {n : Nat} {a b : List Nat} (ha : Good n a) (hb : Good n b)
    (h : setKey a = setKey b) : a = b := by
  have hp : a.Perm b := (List.perm_ext_iff_of_nodup ha.1.nodup hb.1.nodup).2 (mem_of_setKey h)
  exact hp.eq_of_pairwise' (r := (· ≤ ·)) (ha.1.imp le_of_lt) (hb.1.imp le_of_lt)

theorem imgSorted_good {n : Nat} {g : Array Nat} {s : List Nat} (hg : PermA n g) (hs : Good n s) :
    Good n (imgSorted g s) := by
  have hp : (imgSorted g s).Perm (s.map fun p => g[p]!) := List.mergeSort_perm _ _
  have hle : (imgSorted g s).Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (s.map fun p => g[p]!)
    exact this.imp fun h => by simpa using h
  have hnd : (s.map fun p => g[p]!).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy e => hg.2 x (hs.2 x hx) y (hs.2 y hy) e) hs.1.nodup
  refine ⟨?_, fun x hx => ?_⟩
  · exact (hle.and (hp.nodup_iff.2 hnd)).imp fun ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.1 (hp.mem_iff.1 hx)
    exact hg.1 p (hs.2 p hp')

@[expose] def Inv (n : Nat) (gens : Array (Array Nat)) (start : List Nat) (bound : Nat)
    (S : Array (List Nat)) (PA LA : Array Nat) (K : Std.HashSet Co3Key) : Prop :=
  PA.size = S.size ∧ LA.size = S.size ∧ 0 < S.size ∧ S.size ≤ bound ∧ S[0]! = start ∧
    (∀ k, 0 < k → k < S.size →
      PA[k]! < k ∧ LA[k]! < gens.size ∧ S[k]! = imgSorted gens[LA[k]!]! S[PA[k]!]!) ∧
    (∀ x, K.contains ⟨x⟩ = true ↔ ∃ i < S.size, setKey S[i]! = x) ∧
    (∀ i < S.size, Good n S[i]!) ∧
    (∀ i < S.size, ∀ j < S.size, S[i]! = S[j]! → i = j)

theorem push_lt {α : Type} [Inhabited α] {a : Array α} {x : α} {i : Nat} (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), Array.getElem_push_lt h, getElem!_pos a i h]

theorem push_eq {α : Type} [Inhabited α] {a : Array α} {x : α} : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

theorem inv_init {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound : Nat}
    (hb : 0 < bound) (hs : Good n start) :
    Inv n gens start bound #[start] #[0] #[0] ((∅ : Std.HashSet Co3Key).insert ⟨setKey start⟩) := by
  refine ⟨rfl, rfl, by simp, by simp; omega, rfl, fun k h1 h2 => by simp at h2; omega,
    fun x => ?_, fun i hi => ?_, fun i hi j hj _ => ?_⟩
  · rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false, key_beq]
    constructor
    · intro h
      exact ⟨0, by simp, by simpa using h⟩
    · rintro ⟨i, hi, e⟩
      have : i = 0 := by simp at hi; omega
      subst this
      simpa using e
  · have : i = 0 := by simp at hi; omega
    subst this
    simpa using hs
  · simp at hi hj
    omega

theorem inv_push {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound : Nat}
    {S : Array (List Nat)} {PA LA : Array Nat} {K : Std.HashSet Co3Key} {h k : Nat}
    (hI : Inv n gens start bound S PA LA K) (hg : ∀ k < gens.size, PermA n gens[k]!)
    (hsz : S.size < bound) (hh : h < S.size) (hk : k < gens.size)
    (hn : K.contains ⟨setKey (imgSorted gens[k]! S[h]!)⟩ = false) :
    Inv n gens start bound (S.push (imgSorted gens[k]! S[h]!)) (PA.push h) (LA.push k)
      (K.insert ⟨setKey (imgSorted gens[k]! S[h]!)⟩) := by
  obtain ⟨hP, hL, h0, hle, hz, hrec, hK, hgood, hdist⟩ := hI
  set t := imgSorted gens[k]! S[h]! with ht
  have hnew : ∀ i < S.size, S[i]! ≠ t := fun i hi e => by
    have := (hK (setKey t)).2 ⟨i, hi, by rw [e]⟩
    rw [hn] at this
    exact absurd this (by decide)
  refine ⟨by simp [hP], by simp [hL], by simp, by simp; omega, by rw [push_lt h0, hz], ?_, ?_, ?_, ?_⟩
  · intro k' h1 h2
    simp only [Array.size_push] at h2
    rcases Nat.lt_or_ge k' S.size with a | a
    · obtain ⟨b1, b2, b3⟩ := hrec k' h1 a
      rw [push_lt (by omega : k' < PA.size), push_lt (by omega : k' < LA.size), push_lt a,
        push_lt (by omega : PA[k']! < S.size)]
      exact ⟨b1, b2, b3⟩
    · have e : k' = S.size := by omega
      subst e
      rw [← hP, push_eq, hP, ← hL, push_eq, hL, push_eq, push_lt hh]
      exact ⟨hh, hk, rfl⟩
  · intro x
    rw [Std.HashSet.contains_insert, key_beq, Bool.or_eq_true, decide_eq_true_eq, hK]
    constructor
    · rintro (e | ⟨i, hi, e⟩)
      · exact ⟨S.size, by simp, by rw [push_eq]; exact e⟩
      · exact ⟨i, by simp; omega, by rw [push_lt hi]; exact e⟩
    · rintro ⟨i, hi, e⟩
      simp only [Array.size_push] at hi
      rcases Nat.lt_or_ge i S.size with a | a
      · exact Or.inr ⟨i, a, by rw [← push_lt a]; exact e⟩
      · have : i = S.size := by omega
        subst this
        rw [push_eq] at e
        exact Or.inl e
  · intro i hi
    simp only [Array.size_push] at hi
    rcases Nat.lt_or_ge i S.size with a | a
    · rw [push_lt a]
      exact hgood i a
    · have : i = S.size := by omega
      subst this
      rw [push_eq]
      exact imgSorted_good (hg k hk) (hgood h hh)
  · intro i hi j hj e
    simp only [Array.size_push] at hi hj
    rcases Nat.lt_or_ge i S.size with a | a <;> rcases Nat.lt_or_ge j S.size with b | b
    · rw [push_lt a, push_lt b] at e
      exact hdist i a j b e
    · have : j = S.size := by omega
      subst this
      rw [push_lt a, push_eq] at e
      exact absurd e (hnew i a)
    · have : i = S.size := by omega
      subst this
      rw [push_lt b, push_eq] at e
      exact absurd e.symm (hnew j b)
    · omega

abbrev St := Array (List Nat) × Array Nat × Array Nat × Std.HashSet Co3Key

@[expose] def innerBody (gens : Array (Array Nat)) (bound : Nat) (S : Array (List Nat)) (H k : Nat)
    (st : St) : Id (ForInStep St) :=
  if st.1.size < bound then
    if (!st.2.2.2.contains ⟨setKey (imgSorted gens[k]! S[H]!)⟩) = true then
      pure (ForInStep.yield (st.1.push (imgSorted gens[k]! S[H]!), st.2.1.push H, st.2.2.1.push k,
        st.2.2.2.insert ⟨setKey (imgSorted gens[k]! S[H]!)⟩))
    else pure (ForInStep.yield (st.1, st.2.1, st.2.2.1, st.2.2.2))
  else pure (ForInStep.yield (st.1, st.2.1, st.2.2.1, st.2.2.2))

abbrev OSt := Array (List Nat) × Array Nat × Array Nat × Std.HashSet Co3Key × Nat

@[expose] def OSt.inner (s : OSt) : St := (s.1, s.2.1, s.2.2.1, s.2.2.2.1)

@[expose] def outerBody (gens : Array (Array Nat)) (bound : Nat) (_ : Nat) (s : OSt) :
    Id (ForInStep OSt) :=
  if (decide (s.2.2.2.2 < s.1.size) && decide (s.1.size < bound)) = true then
    pure (ForInStep.yield (let t := Id.run (forIn (List.range' 0 gens.size)
      (s.1, s.2.1, s.2.2.1, s.2.2.2.1) (innerBody gens bound s.1 s.2.2.2.2))
      (t.1, t.2.1, t.2.2.1, t.2.2.2, s.2.2.2.2 + 1)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

theorem inner_spec {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound : Nat}
    {S : Array (List Nat)} {PA LA : Array Nat} {K : Std.HashSet Co3Key} {H : Nat}
    (hI : Inv n gens start bound S PA LA K) (hg : ∀ k < gens.size, PermA n gens[k]!)
    (hH : H < S.size) :
    let t := Id.run (forIn (List.range' 0 gens.size) (S, PA, LA, K) (innerBody gens bound S H))
    Inv n gens start bound t.1 t.2.1 t.2.2.1 t.2.2.2 ∧ S.size ≤ t.1.size ∧
      (∀ i < S.size, t.1[i]! = S[i]!) ∧
      (t.1.size < bound → ∀ k < gens.size, ∃ i < t.1.size, t.1[i]! = imgSorted gens[k]! S[H]!) := by
  refine forIn_range'_ind gens.size 0 (S, PA, LA, K) (innerBody gens bound S H)
    (fun j st => Inv n gens start bound st.1 st.2.1 st.2.2.1 st.2.2.2 ∧ S.size ≤ st.1.size ∧
      (∀ i < S.size, st.1[i]! = S[i]!) ∧
      (st.1.size < bound → ∀ k < j, ∃ i < st.1.size, st.1[i]! = imgSorted gens[k]! S[H]!))
    (fun j hj st hP => ?_) ⟨hI, le_refl _, fun i _ => rfl, fun _ k hk => absurd hk (by omega)⟩
  obtain ⟨hI', hle, hpre, hcl⟩ := hP
  have hSH : st.1[H]! = S[H]! := hpre H hH
  have hgood : Good n (imgSorted gens[j]! S[H]!) := by
    rw [← hSH]
    exact imgSorted_good (hg j hj) (hI'.2.2.2.2.2.2.2.1 H (by omega))
  rw [Nat.zero_add]
  by_cases h1 : st.1.size < bound
  · by_cases h2 : st.2.2.2.contains ⟨setKey (imgSorted gens[j]! S[H]!)⟩ = true
    · refine ⟨st, by simp [innerBody, h1, h2], hI', hle, hpre, fun hs k hk => ?_⟩
      rcases Nat.lt_or_ge k j with a | a
      · exact hcl hs k a
      · have e : k = j := by omega
        subst e
        obtain ⟨i, hi, e⟩ := (hI'.2.2.2.2.2.2.1 _).1 h2
        exact ⟨i, hi, eq_of_setKey (hI'.2.2.2.2.2.2.2.1 i hi) hgood e⟩
    · have h2' : st.2.2.2.contains ⟨setKey (imgSorted gens[j]! S[H]!)⟩ = false := by simpa using h2
      refine ⟨(st.1.push (imgSorted gens[j]! S[H]!), st.2.1.push H, st.2.2.1.push j,
        st.2.2.2.insert ⟨setKey (imgSorted gens[j]! S[H]!)⟩), by simp [innerBody, h1, h2'], ?_, ?_,
        ?_, ?_⟩
      · have := inv_push hI' hg h1 (by omega : H < st.1.size) hj (by rw [hSH]; exact h2')
        rw [hSH] at this
        exact this
      · simp only [Array.size_push]
        omega
      · intro i hi
        rw [push_lt (by omega)]
        exact hpre i hi
      · intro hs k hk
        simp only [Array.size_push] at hs
        rcases Nat.lt_or_ge k j with a | a
        · obtain ⟨i, hi, e⟩ := hcl (by omega) k a
          exact ⟨i, by simp; omega, by rw [push_lt hi]; exact e⟩
        · have e : k = j := by omega
          subst e
          exact ⟨st.1.size, by simp, push_eq⟩
  · refine ⟨st, by simp [innerBody, h1], hI', hle, hpre, fun hs => absurd hs h1⟩

@[expose] def OInv (n : Nat) (gens : Array (Array Nat)) (start : List Nat) (bound j : Nat)
    (s : OSt) : Prop :=
  Inv n gens start bound s.1 s.2.1 s.2.2.1 s.2.2.2.1 ∧ s.2.2.2.2 ≤ s.1.size ∧
    (s.1.size = bound ∨ s.2.2.2.2 = j ∨ s.2.2.2.2 = s.1.size) ∧
    (s.1.size < bound → ∀ i < s.2.2.2.2, ∀ k < gens.size,
      ∃ i' < s.1.size, s.1[i']! = imgSorted gens[k]! s.1[i]!)

@[expose] def oinit (start : List Nat) : OSt :=
  (#[start], #[0], #[0], (∅ : Std.HashSet Co3Key).insert ⟨setKey start⟩, 0)

theorem outer_spec {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound : Nat}
    (hb : 0 < bound) (hg : ∀ k < gens.size, PermA n gens[k]!) (hs : Good n start) :
    OInv n gens start bound bound
      (Id.run (forIn (List.range' 0 bound) (oinit start) (outerBody gens bound))) := by
  refine forIn_range'_ind bound 0 _ (outerBody gens bound) (OInv n gens start bound)
    (fun j hj s hQ => ?_)
    ⟨inv_init hb hs, by simp [oinit], Or.inr (Or.inl rfl), fun _ i hi => absurd hi (by simp [oinit] at hi)⟩
  obtain ⟨hI, hle, hor, hcl⟩ := hQ
  rw [Nat.zero_add]
  by_cases hc : s.2.2.2.2 < s.1.size ∧ s.1.size < bound
  · obtain ⟨hc1, hc2⟩ := hc
    obtain ⟨hI', hle', hpre, hcl'⟩ := inner_spec (H := s.2.2.2.2) hI hg hc1
    refine ⟨_, by simp [outerBody, hc1, hc2]; rfl, hI', by simp only; omega, ?_, ?_⟩
    · rcases hor with e | e | e
      · omega
      · exact Or.inr (Or.inl (by simp only [e]))
      · omega
    · intro hs' i hi k hk
      simp only at hs' hi ⊢
      rcases Nat.lt_or_ge i s.2.2.2.2 with a | a
      · obtain ⟨i', hi', e⟩ := hcl (by omega) i a k hk
        refine ⟨i', by omega, ?_⟩
        rw [hpre i' hi', hpre i (by omega), e]
      · have e : i = s.2.2.2.2 := by omega
        subst e
        obtain ⟨i', hi', e⟩ := hcl' hs' k hk
        exact ⟨i', hi', by rw [e, hpre _ hc1]⟩
  · refine ⟨_, by simp [outerBody]; intro h; omega, hI, hle, ?_, hcl⟩
    rcases hor with e | e | e
    · exact Or.inl e
    · have := hI.2.2.2.1
      by_cases h' : s.2.2.2.2 < s.1.size
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inr e)

theorem search_eq (gens : Array (Array Nat)) (start : List Nat) (bound : Nat) :
    co3KeySearch gens start bound =
      let s := Id.run (forIn (List.range' 0 bound) (oinit start) (outerBody gens bound))
      (s.1, s.2.1, s.2.2.1) := by
  unfold co3KeySearch
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem allLt_true {m : Nat} {p : Nat → Bool} (h : ∀ i < m, p i = true) :
    CFSG.Monster.B.Co2.Native.allLt m p = true := by
  unfold CFSG.Monster.B.Co2.Native.allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  exact fun i _ => h i i.isLt

theorem strictlyIncreasing_of {l : List Nat} (h : l.Pairwise (· < ·)) :
    strictlyIncreasing l = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      simp only [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, ih h.of_cons⟩

theorem keySearch_spec {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound : Nat}
    (hb : 0 < bound) (hg : ∀ k < gens.size, PermA n gens[k]!) (hs : Good n start) :
    translatesOK gens start (co3KeySearch gens start bound).1 (co3KeySearch gens start bound).2.1
        (co3KeySearch gens start bound).2.2 = true ∧
      keysSortedOK (co3KeySearch gens start bound).1 = true ∧
      ((∀ F : Finset (List Nat), start ∈ F → (∀ s ∈ F, ∀ k < gens.size, imgSorted gens[k]! s ∈ F) →
        bound ≤ F.card) → (co3KeySearch gens start bound).1.size = bound) := by
  rw [search_eq]
  obtain ⟨hI, hle, hor, hcl⟩ := outer_spec hb hg hs
  generalize Id.run (forIn (List.range' 0 bound) (oinit start) (outerBody gens bound)) = s at hI hle hor hcl ⊢
  obtain ⟨hP, hL, h0, hbd, hz, hrec, hK, hgood, hdist⟩ := hI
  have hget : ∀ i (hi : i < s.1.toList.length), s.1.toList[i] = s.1[i]! := fun i hi => by
    rw [Array.getElem_toList, getElem!_pos s.1 i (by simpa using hi)]
  have hnd : s.1.toList.Nodup := by
    refine List.pairwise_iff_getElem.2 fun i j hi hj hij e => ?_
    rw [hget i hi, hget j hj] at e
    have := hdist i (by simpa using hi) j (by simpa using hj) e
    omega
  have hmem : ∀ x ∈ s.1.toList, ∃ i < s.1.size, s.1[i]! = x := fun x hx => by
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hx
    exact ⟨i, by simpa using hi, by rw [← hget i hi, e]⟩
  refine ⟨?_, ?_, fun hF => ?_⟩
  · unfold translatesOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨h0, hz⟩, allLt_true fun k hk => ?_⟩
    rcases Nat.eq_zero_or_pos k with e | e
    · simp [e]
    · obtain ⟨a, b, c⟩ := hrec k e hk
      simp [a, b, c]
  · unfold keysSortedOK sortedKeys
    apply strictlyIncreasing_of
    have hle' := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (s.1.toList.map setKey)
    have hnd' : (s.1.toList.map setKey).Nodup := by
      refine List.Nodup.map_on (fun x hx y hy e => ?_) hnd
      obtain ⟨i, hi, rfl⟩ := hmem x hx
      obtain ⟨j, hj, rfl⟩ := hmem y hy
      exact eq_of_setKey (hgood i hi) (hgood j hj) e
    have hp := List.mergeSort_perm (s.1.toList.map setKey) (fun a b : Nat => decide (a ≤ b))
    exact (hle'.and (hp.nodup_iff.2 hnd')).imp fun ⟨h1, h2⟩ => lt_of_le_of_ne (by simpa using h1) h2
  · rcases hor with e | e | e
    · exact e
    · by_contra hne
      have hlt : s.1.size < bound := lt_of_le_of_ne hbd hne
      omega
    · by_contra hne
      have hlt : s.1.size < bound := lt_of_le_of_ne hbd hne
      have hcard : s.1.toList.toFinset.card = s.1.size := by
        rw [List.toFinset_card_of_nodup hnd, Array.length_toList]
      have := hF s.1.toList.toFinset (by
          rw [List.mem_toFinset, ← hz]
          rw [← hget 0 (by simpa using h0)]
          exact List.getElem_mem _)
        (fun x hx k hk => by
          obtain ⟨i, hi, rfl⟩ := hmem x (List.mem_toFinset.1 hx)
          obtain ⟨i', hi', e'⟩ := hcl hlt i (by omega) k hk
          rw [List.mem_toFinset, ← e', ← hget i' (by simpa using hi')]
          exact List.getElem_mem _)
      omega

end CFSG.KS.SporSch.KeySearch
