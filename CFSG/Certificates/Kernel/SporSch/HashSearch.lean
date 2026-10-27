
module

public import CFSG.Certificates.Kernel.SporSch.KeySearch

public section

namespace CFSG.KS.SporSch.HashSearch

open CFSG.Sporadic.Schreier.Co3.Native CFSG.Certificates.Native
open CFSG.KS.SporSch.KeySearch

theorem key_beq (a b : Nat) : (a == b) = decide (a = b) := by
  by_cases h : a = b
  · subst h
    simp
  · simp [h]

@[expose] def Inv (n : Nat) (gens : Array (Array Nat)) (start : List Nat) (bound : Nat)
    (S : Array (List Nat)) (PA LA : Array Nat) (K : Std.HashSet Nat) : Prop :=
  PA.size = S.size ∧ LA.size = S.size ∧ 0 < S.size ∧ S.size ≤ bound ∧ S[0]! = start ∧
    (∀ k, 0 < k → k < S.size →
      PA[k]! < k ∧ LA[k]! < gens.size ∧ S[k]! = imgSorted gens[LA[k]!]! S[PA[k]!]!) ∧
    (∀ x, K.contains x = true ↔ ∃ i < S.size, setKey S[i]! = x) ∧
    (∀ i < S.size, Good n S[i]!) ∧
    (∀ i < S.size, ∀ j < S.size, S[i]! = S[j]! → i = j)

theorem inv_init {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound : Nat}
    (hb : 0 < bound) (hs : Good n start) :
    Inv n gens start bound #[start] #[0] #[0] ((∅ : Std.HashSet Nat).insert (setKey start)) := by
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
    {S : Array (List Nat)} {PA LA : Array Nat} {K : Std.HashSet Nat} {h k : Nat}
    (hI : Inv n gens start bound S PA LA K) (hg : ∀ k < gens.size, PermA n gens[k]!)
    (hsz : S.size < bound) (hh : h < S.size) (hk : k < gens.size)
    (hn : K.contains (setKey (imgSorted gens[k]! S[h]!)) = false) :
    Inv n gens start bound (S.push (imgSorted gens[k]! S[h]!)) (PA.push h) (LA.push k)
      (K.insert (setKey (imgSorted gens[k]! S[h]!))) := by
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

abbrev St := Array (List Nat) × Array Nat × Array Nat × Std.HashSet Nat

@[expose] def innerBody (gens : Array (Array Nat)) (bound : Nat) (S : Array (List Nat)) (H k : Nat)
    (st : St) : Id (ForInStep St) :=
  if st.1.size < bound then
    if (!st.2.2.2.contains (setKey (imgSorted gens[k]! S[H]!))) = true then
      pure (ForInStep.yield (st.1.push (imgSorted gens[k]! S[H]!), st.2.1.push H, st.2.2.1.push k,
        st.2.2.2.insert (setKey (imgSorted gens[k]! S[H]!))))
    else pure (ForInStep.yield (st.1, st.2.1, st.2.2.1, st.2.2.2))
  else pure (ForInStep.yield (st.1, st.2.1, st.2.2.1, st.2.2.2))

abbrev OSt := Array (List Nat) × Array Nat × Array Nat × Std.HashSet Nat × Nat

@[expose] def outerBody (gens : Array (Array Nat)) (bound : Nat) (_ : Nat) (s : OSt) :
    Id (ForInStep OSt) :=
  if (decide (s.2.2.2.2 < s.1.size) && decide (s.1.size < bound)) = true then
    pure (ForInStep.yield (let t := Id.run (forIn (List.range' 0 gens.size)
      (s.1, s.2.1, s.2.2.1, s.2.2.2.1) (innerBody gens bound s.1 s.2.2.2.2))
      (t.1, t.2.1, t.2.2.1, t.2.2.2, s.2.2.2.2 + 1)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

theorem inner_spec {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound : Nat}
    {S : Array (List Nat)} {PA LA : Array Nat} {K : Std.HashSet Nat} {H : Nat}
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
  · by_cases h2 : st.2.2.2.contains (setKey (imgSorted gens[j]! S[H]!)) = true
    · refine ⟨st, by simp [innerBody, h1, h2], hI', hle, hpre, fun hs k hk => ?_⟩
      rcases Nat.lt_or_ge k j with a | a
      · exact hcl hs k a
      · have e : k = j := by omega
        subst e
        obtain ⟨i, hi, e⟩ := (hI'.2.2.2.2.2.2.1 _).1 h2
        exact ⟨i, hi, eq_of_setKey (hI'.2.2.2.2.2.2.2.1 i hi) hgood e⟩
    · have h2' : st.2.2.2.contains (setKey (imgSorted gens[j]! S[H]!)) = false := by simpa using h2
      refine ⟨(st.1.push (imgSorted gens[j]! S[H]!), st.2.1.push H, st.2.2.1.push j,
        st.2.2.2.insert (setKey (imgSorted gens[j]! S[H]!))), by simp [innerBody, h1, h2'], ?_, ?_,
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
  (#[start], #[0], #[0], (∅ : Std.HashSet Nat).insert (setKey start), 0)

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
    hashSearch gens start bound =
      let s := Id.run (forIn (List.range' 0 bound) (oinit start) (outerBody gens bound))
      (s.1, s.2.1, s.2.2.1) := by
  unfold hashSearch
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

end CFSG.KS.SporSch.HashSearch

end
