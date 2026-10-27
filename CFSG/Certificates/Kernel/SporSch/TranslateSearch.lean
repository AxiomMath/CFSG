module

public import CFSG.Certificates.Kernel.SporSch.SetReplayProof

public section

namespace CFSG.KS.SporSch.TranslateSearch

open CFSG.Certificates.Native CFSG.KS.SporSch.KeySearch

theorem contains_iff {S : Array (List Nat)} {t : List Nat} :
    S.contains t = true ↔ ∃ i < S.size, S[i]! = t := by
  rw [Array.contains_iff_mem, Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, e⟩
    exact ⟨i, hi, by rw [getElem!_pos S i hi, e]⟩
  · rintro ⟨i, hi, e⟩
    exact ⟨i, hi, by rw [← getElem!_pos S i hi, e]⟩

@[expose] def Inv (n : Nat) (gens : Array (Array Nat)) (start : List Nat) (bound : Nat)
    (S : Array (List Nat)) (PA LA : Array Nat) : Prop :=
  PA.size = S.size ∧ LA.size = S.size ∧ 0 < S.size ∧ S.size ≤ bound ∧ S[0]! = start ∧
    (∀ k, 0 < k → k < S.size →
      PA[k]! < k ∧ LA[k]! < gens.size ∧ S[k]! = imgSorted gens[LA[k]!]! S[PA[k]!]!) ∧
    (∀ i < S.size, Good n S[i]!) ∧
    (∀ i < S.size, ∀ j < S.size, S[i]! = S[j]! → i = j)

theorem inv_init {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound : Nat}
    (hb : 0 < bound) (hs : Good n start) : Inv n gens start bound #[start] #[0] #[0] := by
  refine ⟨rfl, rfl, by simp, by simp; omega, rfl, fun k h1 h2 => by simp at h2; omega,
    fun i hi => ?_, fun i hi j hj _ => ?_⟩
  · have : i = 0 := by simp at hi; omega
    subst this
    simpa using hs
  · simp at hi hj
    omega

theorem inv_push {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound : Nat}
    {S : Array (List Nat)} {PA LA : Array Nat} {h k : Nat}
    (hI : Inv n gens start bound S PA LA) (hg : ∀ k < gens.size, PermA n gens[k]!)
    (hsz : S.size < bound) (hh : h < S.size) (hk : k < gens.size)
    (hn : S.contains (imgSorted gens[k]! S[h]!) = false) :
    Inv n gens start bound (S.push (imgSorted gens[k]! S[h]!)) (PA.push h) (LA.push k) := by
  obtain ⟨hP, hL, h0, hle, hz, hrec, hgood, hdist⟩ := hI
  set t := imgSorted gens[k]! S[h]! with ht
  have hnew : ∀ i < S.size, S[i]! ≠ t := fun i hi e => by
    have := contains_iff.2 ⟨i, hi, e⟩
    rw [hn] at this
    exact absurd this (by decide)
  refine ⟨by simp [hP], by simp [hL], by simp, by simp; omega, by rw [push_lt h0, hz], ?_, ?_, ?_⟩
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

abbrev St := Array (List Nat) × Array Nat × Array Nat

@[expose] def innerBody (gens : Array (Array Nat)) (bound : Nat) (S : Array (List Nat)) (H k : Nat)
    (st : St) : Id (ForInStep St) :=
  if st.1.size < bound then
    if (!st.1.contains (imgSorted gens[k]! S[H]!)) = true then
      pure (ForInStep.yield (st.1.push (imgSorted gens[k]! S[H]!), st.2.1.push H, st.2.2.push k))
    else pure (ForInStep.yield (st.1, st.2.1, st.2.2))
  else pure (ForInStep.yield (st.1, st.2.1, st.2.2))

abbrev OSt := Array (List Nat) × Array Nat × Array Nat × Nat

@[expose] def outerBody (gens : Array (Array Nat)) (bound : Nat) (_ : Nat) (s : OSt) :
    Id (ForInStep OSt) :=
  if (decide (s.2.2.2 < s.1.size) && decide (s.1.size < bound)) = true then
    pure (ForInStep.yield (let t := Id.run (forIn (List.range' 0 gens.size)
      (s.1, s.2.1, s.2.2.1) (innerBody gens bound s.1 s.2.2.2))
      (t.1, t.2.1, t.2.2, s.2.2.2 + 1)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

theorem inner_spec {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound : Nat}
    {S : Array (List Nat)} {PA LA : Array Nat} {H : Nat}
    (hI : Inv n gens start bound S PA LA) (hg : ∀ k < gens.size, PermA n gens[k]!)
    (hH : H < S.size) :
    let t := Id.run (forIn (List.range' 0 gens.size) (S, PA, LA) (innerBody gens bound S H))
    Inv n gens start bound t.1 t.2.1 t.2.2 ∧ S.size ≤ t.1.size ∧
      (∀ i < S.size, t.1[i]! = S[i]!) ∧
      (t.1.size < bound → ∀ k < gens.size, ∃ i < t.1.size, t.1[i]! = imgSorted gens[k]! S[H]!) := by
  refine forIn_range'_ind gens.size 0 (S, PA, LA) (innerBody gens bound S H)
    (fun j st => Inv n gens start bound st.1 st.2.1 st.2.2 ∧ S.size ≤ st.1.size ∧
      (∀ i < S.size, st.1[i]! = S[i]!) ∧
      (st.1.size < bound → ∀ k < j, ∃ i < st.1.size, st.1[i]! = imgSorted gens[k]! S[H]!))
    (fun j hj st hP => ?_) ⟨hI, le_refl _, fun i _ => rfl, fun _ k hk => absurd hk (by omega)⟩
  obtain ⟨hI', hle, hpre, hcl⟩ := hP
  have hSH : st.1[H]! = S[H]! := hpre H hH
  rw [Nat.zero_add]
  by_cases h1 : st.1.size < bound
  · by_cases h2 : st.1.contains (imgSorted gens[j]! S[H]!) = true
    · have hm : imgSorted gens[j]! S[H]! ∈ st.1 := Array.contains_iff_mem.1 h2
      refine ⟨st, by simp [innerBody, h1, hm], hI', hle, hpre, fun hs k hk => ?_⟩
      rcases Nat.lt_or_ge k j with a | a
      · exact hcl hs k a
      · have e : k = j := by omega
        subst e
        exact contains_iff.1 h2
    · have h2' : st.1.contains (imgSorted gens[j]! S[H]!) = false := by simpa using h2
      have hm : imgSorted gens[j]! S[H]! ∉ st.1 := fun hm => by
        rw [Array.contains_iff_mem.2 hm] at h2'
        exact absurd h2' (by decide)
      refine ⟨(st.1.push (imgSorted gens[j]! S[H]!), st.2.1.push H, st.2.2.push j),
        by simp [innerBody, h1, hm], ?_, ?_, ?_, ?_⟩
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
  Inv n gens start bound s.1 s.2.1 s.2.2.1 ∧ s.2.2.2 ≤ s.1.size ∧
    (s.1.size = bound ∨ s.2.2.2 = j ∨ s.2.2.2 = s.1.size) ∧
    (s.1.size < bound → ∀ i < s.2.2.2, ∀ k < gens.size,
      ∃ i' < s.1.size, s.1[i']! = imgSorted gens[k]! s.1[i]!)

@[expose] def oinit (start : List Nat) : OSt := (#[start], #[0], #[0], 0)

theorem outer_spec {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound : Nat}
    (hb : 0 < bound) (hg : ∀ k < gens.size, PermA n gens[k]!) (hs : Good n start) :
    OInv n gens start bound bound
      (Id.run (forIn (List.range' 0 bound) (oinit start) (outerBody gens bound))) := by
  refine forIn_range'_ind bound 0 _ (outerBody gens bound) (OInv n gens start bound)
    (fun j hj s hQ => ?_)
    ⟨inv_init hb hs, by simp [oinit], Or.inr (Or.inl rfl), fun _ i hi => absurd hi (by simp [oinit] at hi)⟩
  obtain ⟨hI, hle, hor, hcl⟩ := hQ
  rw [Nat.zero_add]
  by_cases hc : s.2.2.2 < s.1.size ∧ s.1.size < bound
  · obtain ⟨hc1, hc2⟩ := hc
    obtain ⟨hI', hle', hpre, hcl'⟩ := inner_spec (H := s.2.2.2) hI hg hc1
    refine ⟨_, by simp [outerBody, hc1, hc2]; rfl, hI', by simp only; omega, ?_, ?_⟩
    · rcases hor with e | e | e
      · omega
      · exact Or.inr (Or.inl (by simp only [e]))
      · omega
    · intro hs' i hi k hk
      simp only at hs' hi ⊢
      rcases Nat.lt_or_ge i s.2.2.2 with a | a
      · obtain ⟨i', hi', e⟩ := hcl (by omega) i a k hk
        refine ⟨i', by omega, ?_⟩
        rw [hpre i' hi', hpre i (by omega), e]
      · have e : i = s.2.2.2 := by omega
        subst e
        obtain ⟨i', hi', e⟩ := hcl' hs' k hk
        exact ⟨i', hi', by rw [e, hpre _ hc1]⟩
  · refine ⟨_, by simp [outerBody]; intro h; omega, hI, hle, ?_, hcl⟩
    rcases hor with e | e | e
    · exact Or.inl e
    · have := hI.2.2.2.1
      by_cases h' : s.2.2.2 < s.1.size
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inr e)

theorem search_eq (gens : Array (Array Nat)) (start : List Nat) (bound : Nat) :
    translateSearch gens start bound =
      let s := Id.run (forIn (List.range' 0 bound) (oinit start) (outerBody gens bound))
      (s.1, s.2.1, s.2.2.1) := by
  unfold translateSearch
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

end CFSG.KS.SporSch.TranslateSearch

namespace CFSG.KS.SporSch.SRP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.SporSch.KeySearch
open CFSG.Certificates.Native

theorem translateReplay_proved {n w s kg c bound nS H nB B R : Nat}
    {G GI X W SO SOI C : Nat → Nat} {start : List Nat} {gens : Array (Array Nat)}
    (hg : gens.size = kg ∧ ∀ k < kg, gens[k]! = unpack n w (G k))
    (h : SetReplayOK n w s kg c bound nS H nB B R G GI X W SO SOI C start) :
    translatesOK gens start (translateSearch gens start bound).1
        (translateSearch gens start bound).2.1 (translateSearch gens start bound).2.2 = true ∧
      (translateSearch gens start bound).1.toList.Nodup ∧
      (translateSearch gens start bound).1.size = c := by
  obtain ⟨hc0, hcb, hpA, hgood, hT0, htree, hinj, hclose⟩ := replay_facts hg h
  have hs : Good n start := hT0 ▸ hgood 0 hc0
  rw [TranslateSearch.search_eq]
  obtain ⟨hI, hle, hor, hcl⟩ := TranslateSearch.outer_spec (bound := bound) (by omega) hpA hs
  generalize Id.run (forIn (List.range' 0 bound) (TranslateSearch.oinit start)
    (TranslateSearch.outerBody gens bound)) = st at hI hle hor hcl ⊢
  obtain ⟨-, -, h0, hbd, hz, hrec, hgd, hdist⟩ := hI
  obtain ⟨h1, -, h3⟩ := assemble h0 hbd hz hrec hgd hdist hle hor hcl hc0 hcb hT0 htree hinj hclose
  refine ⟨h1, List.pairwise_iff_getElem.2 fun i j hi hj hij e => ?_, h3⟩
  rw [Array.getElem_toList, Array.getElem_toList, ← getElem!_pos st.1 i (by simpa using hi),
    ← getElem!_pos st.1 j (by simpa using hj)] at e
  have := hdist i (by simpa using hi) j (by simpa using hj) e
  omega

end CFSG.KS.SporSch.SRP

end
