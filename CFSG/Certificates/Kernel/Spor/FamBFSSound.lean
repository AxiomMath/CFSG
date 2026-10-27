module

public import CFSG.Certificates.Kernel.SporSch.KeySearch
public import CFSG.Sporadic.SuzOddCore.FamilyCheckInputs

public section

namespace CFSG.KS.FamBFS

open CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native CFSG.KS.SporSch.KeySearch

abbrev ISt := Array (List Nat) × Array Bool × Array Nat

abbrev OSt := Array (List Nat) × Array Bool × Array Nat × Nat

@[expose] def innerBody (idxGens setGens : Array (Array Nat)) (d k : Nat) (st : ISt) :
    Id (ForInStep ISt) :=
  if (!st.2.1[(idxGens[k]!)[d]!]!) = true then
    pure (ForInStep.yield ((st.1.set! (idxGens[k]!)[d]! (imgSorted setGens[k]! st.1[d]!)),
      st.2.1.set! (idxGens[k]!)[d]! true, st.2.2.push (idxGens[k]!)[d]!))
  else pure (ForInStep.yield (st.1, st.2.1, st.2.2))

@[expose] def outerBody (idxGens setGens : Array (Array Nat)) (_ : Nat) (s : OSt) :
    Id (ForInStep OSt) :=
  if s.2.2.2 < s.2.2.1.size then
    pure (ForInStep.yield (let t := Id.run (forIn (List.range' 0 idxGens.size)
      (s.1, s.2.1, s.2.2.1) (innerBody idxGens setGens s.2.2.1[s.2.2.2]!))
      (t.1, t.2.1, t.2.2, s.2.2.2 + 1)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def oinit (n : Nat) (seed : List Nat) : OSt :=
  ((Array.replicate n []).set! 0 seed, (Array.replicate n false).set! 0 true, #[0], 0)

theorem search_eq (n : Nat) (idxGens setGens : Array (Array Nat)) (seed : List Nat) :
    famBFS n idxGens setGens seed =
      (Id.run (forIn (List.range' 0 n) (oinit n seed) (outerBody idxGens setGens))).1 := by
  unfold famBFS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

section Inv

variable (n : Nat) (idxGens setGens : Array (Array Nat)) (F : Array (List Nat))

@[expose] def Inv (st : ISt) : Prop :=
  st.1.size = n ∧ st.2.1.size = n ∧ (∀ e < n, st.2.1[e]! = true → st.1[e]! = F[e]!) ∧
    (∀ x ∈ st.2.2.toList, x < n ∧ st.2.1[x]! = true) ∧
    (∀ e < n, st.2.1[e]! = true → e ∈ st.2.2.toList) ∧ st.2.2.toList.Nodup ∧ 0 < st.2.2.size ∧
    st.2.2[0]! = 0

end Inv

theorem setb_get {a : Array Bool} {e x : Nat} (hx : x < a.size) :
    (a.set! e true)[x]! = (if x = e then true else a[x]!) := by
  rw [getElem!_pos _ x (by simpa using hx), getElem!_pos a x hx]
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds]
  by_cases h : x = e
  · subst h
    simp [hx]
  · simp only [h, ↓reduceIte]
    exact Array.getElem_setIfInBounds_ne hx (Ne.symm h)

theorem setl_get {a : Array (List Nat)} {e x : Nat} {v : List Nat} (hx : x < a.size) :
    (a.set! e v)[x]! = (if x = e then v else a[x]!) := by
  rw [getElem!_pos _ x (by simpa using hx), getElem!_pos a x hx]
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds]
  by_cases h : x = e
  · subst h
    simp [hx]
  · simp only [h, ↓reduceIte]
    exact Array.getElem_setIfInBounds_ne hx (Ne.symm h)

theorem inner_spec {n : Nat} {idxGens setGens : Array (Array Nat)} {F : Array (List Nat)}
    (hidx : ∀ k < idxGens.size, ∀ d < n, (idxGens[k]!)[d]! < n)
    (hrec : ∀ k < idxGens.size, ∀ d < n,
      F[(idxGens[k]!)[d]!]! = imgSorted setGens[k]! F[d]!)
    {st : ISt} (hI : Inv n F st) {d : Nat} (hd : d < n) (hds : st.2.1[d]! = true) :
    let t := Id.run (forIn (List.range' 0 idxGens.size) st (innerBody idxGens setGens d))
    Inv n F t ∧ (∀ e < n, st.2.1[e]! = true → t.2.1[e]! = true) ∧
      st.2.2.size ≤ t.2.2.size ∧ (∀ i < st.2.2.size, t.2.2[i]! = st.2.2[i]!) ∧
      (∀ k < idxGens.size, t.2.1[(idxGens[k]!)[d]!]! = true) := by
  refine forIn_range'_ind idxGens.size 0 st (innerBody idxGens setGens d)
    (fun j t => Inv n F t ∧ (∀ e < n, st.2.1[e]! = true → t.2.1[e]! = true) ∧
      st.2.2.size ≤ t.2.2.size ∧ (∀ i < st.2.2.size, t.2.2[i]! = st.2.2[i]!) ∧
      (∀ k < j, t.2.1[(idxGens[k]!)[d]!]! = true))
    (fun j hj t hP => ?_) ⟨hI, fun _ _ h => h, le_refl _, fun _ _ => rfl, fun _ hk => absurd hk (by omega)⟩
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, hmono, hle, hpre, hcl⟩ := hP
  rw [Nat.zero_add]
  have he : (idxGens[j]!)[d]! < n := hidx j hj d hd
  set e := (idxGens[j]!)[d]! with hedef
  have hdt : t.2.1[d]! = true := hmono d hd hds
  by_cases hs : t.2.1[e]! = true
  · refine ⟨t, by simp [innerBody, ← hedef, hs], ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, hmono, hle, hpre,
      fun k hk => ?_⟩
    rcases Nat.lt_or_ge k j with a | a
    · exact hcl k a
    · have : k = j := by omega
      subst this
      exact hs
  · have hs' : t.2.1[e]! = false := by simpa using hs
    have hnq : e ∉ t.2.2.toList := fun hm => by
      rw [(h4 e hm).2] at hs'
      exact absurd hs' (by decide)
    refine ⟨(t.1.set! e (imgSorted setGens[j]! t.1[d]!), t.2.1.set! e true, t.2.2.push e),
      by simp [innerBody, ← hedef, hs'], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp [h1]
    · simp [h2]
    · intro x hx hxs
      simp only at hxs ⊢
      rw [setb_get (by rw [h2]; exact hx)] at hxs
      rw [setl_get (by rw [h1]; exact hx)]
      by_cases hxe : x = e
      · subst hxe
        simp only [↓reduceIte]
        rw [h3 d hd hdt, hrec j hj d hd]
      · simp only [hxe, ↓reduceIte] at hxs ⊢
        exact h3 x hx hxs
    · intro x hx
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · obtain ⟨a, b⟩ := h4 x hx
        refine ⟨a, ?_⟩
        simp only
        rw [setb_get (by rw [h2]; exact a)]
        split <;> simp_all
      · refine ⟨he, ?_⟩
        simp only
        rw [setb_get (by rw [h2]; exact he)]
        simp
    · intro x hx hxs
      simp only at hxs ⊢
      rw [setb_get (by rw [h2]; exact hx)] at hxs
      simp only [Array.toList_push, List.mem_append, List.mem_singleton]
      by_cases hxe : x = e
      · exact Or.inr hxe
      · simp only [hxe, ↓reduceIte] at hxs
        exact Or.inl (h5 x hx hxs)
    · simp only [Array.toList_push]
      exact List.nodup_append.2 ⟨h6, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton] at hb
        subst hb
        exact fun h => hnq (h ▸ ha)⟩
    · simp
    · simp only
      rw [push_lt h7]
      exact h8
    · intro x hx hxs
      simp only
      rw [setb_get (by rw [h2]; exact hx)]
      split
      · rfl
      · exact hmono x hx hxs
    · simp only [Array.size_push]
      omega
    · intro i hi
      simp only
      rw [push_lt (by omega)]
      exact hpre i hi
    · intro k hk
      simp only
      have hk' : (idxGens[k]!)[d]! < n := hidx k (by omega) d hd
      rw [setb_get (by rw [h2]; exact hk')]
      split
      · rfl
      · rcases Nat.lt_or_ge k j with a | a
        · exact hcl k a
        · have : k = j := by omega
          subst this
          contradiction

@[expose] def OInv (n : Nat) (idxGens : Array (Array Nat)) (F : Array (List Nat)) (j : Nat)
    (s : OSt) : Prop :=
  Inv n F (s.1, s.2.1, s.2.2.1) ∧ s.2.2.2 ≤ s.2.2.1.size ∧
    (s.2.2.2 = s.2.2.1.size ∨ j ≤ s.2.2.2) ∧
    (∀ i < s.2.2.2, ∀ k < idxGens.size, s.2.1[(idxGens[k]!)[s.2.2.1[i]!]!]! = true)

theorem queue_le {n : Nat} {F : Array (List Nat)} {st : ISt} (hI : Inv n F st) :
    st.2.2.size ≤ n := by
  obtain ⟨-, -, -, h4, -, h6, -, -⟩ := hI
  have hs : st.2.2.toList.Subperm (List.range n) :=
    List.subperm_of_subset h6 fun x hx => List.mem_range.2 (h4 x hx).1
  simpa using hs.length_le

theorem queue_get {n : Nat} {F : Array (List Nat)} {st : ISt} (hI : Inv n F st) {i : Nat}
    (hi : i < st.2.2.size) : st.2.2[i]! < n ∧ st.2.1[st.2.2[i]!]! = true := by
  refine hI.2.2.2.1 _ ?_
  rw [getElem!_pos _ i hi]
  exact Array.getElem_mem_toList hi

theorem outer_spec {n : Nat} {idxGens setGens : Array (Array Nat)} {F : Array (List Nat)}
    {seed : List Nat} (hn : 0 < n) (hF0 : F[0]! = seed)
    (hidx : ∀ k < idxGens.size, ∀ d < n, (idxGens[k]!)[d]! < n)
    (hrec : ∀ k < idxGens.size, ∀ d < n,
      F[(idxGens[k]!)[d]!]! = imgSorted setGens[k]! F[d]!) :
    OInv n idxGens F n
      (Id.run (forIn (List.range' 0 n) (oinit n seed) (outerBody idxGens setGens))) := by
  have hinit : Inv n F ((oinit n seed).1, (oinit n seed).2.1, (oinit n seed).2.2.1) := by
    refine ⟨by simp [oinit], by simp [oinit], fun e he hs => ?_, fun x hx => ?_,
      fun e he hs => ?_, by simp [oinit], by simp [oinit], by simp [oinit]⟩
    · simp only [oinit] at hs ⊢
      rw [setb_get (by simpa using he)] at hs
      rw [setl_get (by simpa using he)]
      by_cases h : e = 0
      · subst h
        simp [hF0]
      · simp [h, he] at hs
    · simp only [oinit, List.toList_toArray, List.mem_singleton] at hx
      subst hx
      refine ⟨hn, ?_⟩
      simp only [oinit]
      rw [setb_get (by simpa using hn)]
      simp
    · simp only [oinit] at hs ⊢
      rw [setb_get (by simpa using he)] at hs
      by_cases h : e = 0
      · simp [h]
      · simp [h, he] at hs
  refine forIn_range'_ind n 0 _ (outerBody idxGens setGens) (OInv n idxGens F)
    (fun j hj s hQ => ?_) ⟨hinit, by simp [oinit], Or.inr (Nat.zero_le _),
      fun i hi => absurd hi (by simp [oinit])⟩
  obtain ⟨hI, hle, hor, hcl⟩ := hQ
  by_cases hc : s.2.2.2 < s.2.2.1.size
  · obtain ⟨hd, hds⟩ := queue_get hI hc
    obtain ⟨hI', hmono, hsz, hpre, hcl'⟩ := inner_spec (setGens := setGens)
      (d := s.2.2.1[s.2.2.2]!) hidx hrec hI hd hds
    set t := Id.run (forIn (List.range' 0 idxGens.size) (s.1, s.2.1, s.2.2.1)
      (innerBody idxGens setGens s.2.2.1[s.2.2.2]!)) with ht
    have hsz' : s.2.2.1.size ≤ t.2.2.size := hsz
    have hle' : s.2.2.2 ≤ s.2.2.1.size := hle
    refine ⟨(t.1, t.2.1, t.2.2, s.2.2.2 + 1), by rw [outerBody, if_pos hc], hI',
      by dsimp only; omega, ?_, ?_⟩
    · rcases hor with e | e
      · dsimp only
        omega
      · exact Or.inr (by dsimp only; omega)
    · intro i hi k hk
      dsimp only at hi ⊢
      rcases Nat.lt_or_ge i s.2.2.2 with a | a
      · have hia : i < s.2.2.1.size := lt_of_lt_of_le a hle'
        rw [hpre i hia]
        have hq := queue_get hI hia
        exact hmono _ (hidx k hk _ hq.1) (hcl i a k hk)
      · have e : i = s.2.2.2 := by omega
        subst e
        rw [hpre _ hc]
        exact hcl' k hk
  · refine ⟨_, by simp [outerBody, hc], hI, hle, Or.inl (by omega), hcl⟩

theorem famBFS_eq {n : Nat} {idxGens setGens : Array (Array Nat)} {F : Array (List Nat)}
    {seed : List Nat} (hn : 0 < n) (hF : F.size = n) (hF0 : F[0]! = seed)
    (hidx : ∀ k < idxGens.size, ∀ d < n, (idxGens[k]!)[d]! < n)
    (hrec : ∀ k < idxGens.size, ∀ d < n,
      F[(idxGens[k]!)[d]!]! = imgSorted setGens[k]! F[d]!)
    (rk : Nat → Nat)
    (hreach : ∀ e < n, e ≠ 0 → ∃ k < idxGens.size, ∃ d < n, (idxGens[k]!)[d]! = e ∧ rk d < rk e) :
    famBFS n idxGens setGens seed = F := by
  rw [search_eq]
  obtain ⟨hI, hle, hor, hcl⟩ := outer_spec (setGens := setGens) hn hF0 hidx hrec
  set s := Id.run (forIn (List.range' 0 n) (oinit n seed) (outerBody idxGens setGens))
  have hq := queue_le hI
  have hhead : s.2.2.2 = s.2.2.1.size := by
    rcases hor with e | e
    · exact e
    · simp only at hq
      omega
  have hI0 := hI
  obtain ⟨h1, h2, h3, -, h5, -, h7, h8⟩ := hI0
  have hseen : ∀ m, ∀ e < n, rk e = m → s.2.1[e]! = true := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro e he hm
      by_cases h0 : e = 0
      · subst h0
        have := (queue_get hI h7).2
        simp only at this h8
        rwa [h8] at this
      · obtain ⟨k, hk, d, hd, hde, hlt⟩ := hreach e he h0
        have hds := ih (rk d) (by omega) d hd rfl
        obtain ⟨i, hi, hie⟩ := List.getElem_of_mem (h5 d hd hds)
        have hi' : i < s.2.2.1.size := by simpa using hi
        have := hcl i (by rw [hhead]; exact hi') k hk
        rw [getElem!_pos _ i hi', ← Array.getElem_toList, hie, hde] at this
        exact this
  apply Array.ext
  · rw [h1, hF]
  · intro e he _
    have he' : e < n := by rw [h1] at he; exact he
    rw [← getElem!_pos s.1 e he, ← getElem!_pos F e (by rw [hF]; exact he')]
    exact h3 e he' (hseen _ e he' rfl)

end CFSG.KS.FamBFS

end
