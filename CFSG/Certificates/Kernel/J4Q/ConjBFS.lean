module

public import CFSG.Sporadic.J4.QT2LocVLNative
public import CFSG.Certificates.Kernel.J4Q.BfsOrder
import CFSG.Certificates.Kernel.J4Q.VOrbBFS
public import Aesop.BuiltinRules
public import Std.Data.HashSet.Lemmas

public section

namespace CFSG.KC.J4Q.ConjBFS

open CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.KC.J4Q.VOrbBFS

@[expose] def gbfs {β : Type} [Inhabited β] (key : β → List Nat) (mkSeed : List Nat → β)
    (mkNew : List Nat → Nat → Int → β) (seeds : List (List Nat)) (fuel : Nat) : Array β :=
  Id.run do
    let mut seen : Std.HashSet (List Nat) := {}
    let mut arr : Array β := #[]
    for s in seeds do
      if !seen.contains s then
        seen := seen.insert s
        arr := arr.push (mkSeed s)
    let mut i := 0
    for _ in [0:fuel] do
      if i < arr.size then
        let t := key arr[i]!
        for ℓ in letters do
          let u := letConj ℓ t
          if !seen.contains u then
            seen := seen.insert u
            arr := arr.push (mkNew u i ℓ)
        i := i + 1
    return arr

theorem closureConjT_eq (seeds : List (List Nat)) (fuel : Nat) :
    closureConjT seeds fuel = gbfs id id (fun u _ _ => u) seeds fuel := rfl

theorem vlTree_eq (seeds : List (List Nat)) (fuel : Nat) :
    vlTree seeds fuel = gbfs (·.1) (fun s => (s, 0, 0)) (fun u i ℓ => (u, i, ℓ)) seeds fuel := rfl

theorem forIn_list_inv {α β : Type} (I : Nat → β → Prop) (f : α → β → Id (ForInStep β))
    (l : List α) (hstep : ∀ k, k < l.length → ∀ x b, l[k]? = some x → I k b →
      ∃ b', f x b = .yield b' ∧ I (k + 1) b')
    (b : β) (h0 : I 0 b) : I l.length (forIn l b f) := by
  have key : ∀ (suf : List α) (j : Nat) (b : β), j ≤ l.length → l.drop j = suf → I j b →
      I l.length (forIn suf b f) := by
    intro suf
    induction suf with
    | nil =>
      intro j b hjl hd hj
      have hjl' : j = l.length := by
        have := List.drop_eq_nil_iff.1 hd
        omega
      subst hjl'
      exact hj
    | cons a suf ih =>
      intro j b _ hd hj
      have hjl : j < l.length := by
        by_contra hc
        rw [List.drop_eq_nil_of_le (by omega)] at hd
        exact List.cons_ne_nil a suf hd.symm
      have ha : l[j]? = some a := by
        have := congrArg List.head? hd
        rwa [List.head?_drop] at this
      obtain ⟨b', hf, hb'⟩ := hstep j hjl a b ha hj
      rw [List.forIn_cons, hf]
      exact ih (j + 1) b' hjl (by rw [← List.drop_drop, hd]; rfl) hb'
  exact key l 0 b (Nat.zero_le _) rfl h0

theorem forIn_list_bind {α β γ : Type} (I : Nat → β → Prop) (P : γ → Prop)
    (f : α → β → Id (ForInStep β)) (l : List α)
    (hstep : ∀ k, k < l.length → ∀ x b, l[k]? = some x → I k b →
      ∃ b', f x b = .yield b' ∧ I (k + 1) b')
    (b : β) (g : β → Id γ) (hend : ∀ b, I l.length b → P (g b).run) (h0 : I 0 b) :
    P (forIn l b f >>= g).run :=
  hend _ (forIn_list_inv I f l hstep b h0)

variable {β : Type} [Inhabited β] {key : β → List Nat} {mkSeed : List Nat → β}
  {mkNew : List Nat → Nat → Int → β}

@[expose] def SeedInv (mkSeed : List Nat → β) (seeds : List (List Nat)) (k : Nat)
    (st : Std.HashSet (List Nat) × Array β) : Prop :=
  st.2.toList = (seeds.take k).eraseDups.map mkSeed ∧ ∀ x, st.1.contains x = true ↔ x ∈ seeds.take k

omit [Inhabited β] in
theorem seed_step {seeds : List (List Nat)} {k : Nat} (hk : k < seeds.length)
    {st : Std.HashSet (List Nat) × Array β} (hI : SeedInv mkSeed seeds k st) :
    SeedInv mkSeed seeds (k + 1) (if (!st.1.contains seeds[k]) = true then
      (st.1.insert seeds[k], st.2.push (mkSeed seeds[k])) else (st.1, st.2)) := by
  · obtain ⟨h1, h2⟩ := hI
    change _ ∧ _
    have ht : seeds.take (k + 1) = seeds.take k ++ [seeds[k]] := List.take_succ_eq_append_getElem hk
    rw [ht, List.eraseDups_append]
    by_cases hm : seeds[k] ∈ seeds.take k
    · have hc : st.1.contains seeds[k] = true := (h2 _).2 hm
      simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hr : [seeds[k]].removeAll (seeds.take k) = [] := by
        simp [List.removeAll, hm]
      refine ⟨by rw [hr, h1]; simp, fun x => ?_⟩
      rw [h2 x, List.mem_append, List.mem_singleton]
      constructor
      · exact Or.inl
      · rintro (h | rfl)
        · exact h
        · exact hm
    · have hc : st.1.contains seeds[k] = false := by
        cases e : st.1.contains seeds[k]
        · rfl
        · exact absurd ((h2 _).1 e) hm
      simp only [hc, Bool.not_false, ↓reduceIte]
      have hr : [seeds[k]].removeAll (seeds.take k) = [seeds[k]] := by
        simp [List.removeAll, hm]
      refine ⟨?_, fun x => ?_⟩
      · rw [hr, Array.toList_push, h1, List.map_append]
        rfl
      · rw [Std.HashSet.contains_insert, Bool.or_eq_true, h2 x, List.mem_append, List.mem_singleton,
          beq_iff_eq, eq_comm, or_comm]

@[expose] def entry (mkSeed : List Nat → β) (mkNew : List Nat → Nat → Int → β)
    (TS : Nat → List Nat) (PAR LAB : Nat → Nat) (s k : Nat) : β :=
  if k < s then mkSeed (TS k) else mkNew (TS k) (PAR k) (letters.getD (LAB k) 0)

@[expose] def StInv (E : Nat → β) (TS : Nat → List Nat) (m : Nat) (seen : Std.HashSet (List Nat))
    (arr : Array β) : Prop :=
  arr.size = m ∧ arr.toList = (List.range m).map E ∧ ∀ x, seen.contains x = true ↔ ∃ j < m, TS j = x

theorem stInv_get {E : Nat → β} {TS : Nat → List Nat} {m : Nat} {seen : Std.HashSet (List Nat)}
    {arr : Array β} (h : StInv E TS m seen arr) {i : Nat} (hi : i < m) : arr[i]! = E i := by
  have hs := h.1
  rw [getElem!_pos arr i (by omega), ← Array.getElem_toList]
  simp only [h.2.1, List.getElem_map, List.getElem_range]

omit [Inhabited β] in
theorem stInv_push {E : Nat → β} {TS : Nat → List Nat} {m : Nat} {seen : Std.HashSet (List Nat)}
    {arr : Array β} (h : StInv E TS m seen arr) :
    StInv E TS (m + 1) (seen.insert (TS m)) (arr.push (E m)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [Array.size_push, h1], by rw [Array.toList_push, h2, List.range_succ, List.map_append,
    List.map_singleton], fun x => ?_⟩
  rw [Std.HashSet.contains_insert, Bool.or_eq_true, h3 x, beq_iff_eq]
  constructor
  · rintro (h | ⟨j, hj, hx⟩)
    · exact ⟨m, by omega, h⟩
    · exact ⟨j, by omega, hx⟩
  · rintro ⟨j, hj, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact Or.inr ⟨j, hj, hx⟩
    · exact Or.inl hx

theorem letters_length : letters.length = 6 := rfl

theorem gbfs_sound (hkS : ∀ x, key (mkSeed x) = x) (hkN : ∀ u i ℓ, key (mkNew u i ℓ) = u)
    {seeds : List (List Nat)} {fuel n s : Nat} {TS : Nat → List Nat} {PAR LAB : Nat → Nat}
    {TT : Nat → Nat → Nat}
    (hseeds : seeds.eraseDups = (List.range s).map TS) (hsn : s ≤ n)
    (hdist : ∀ i < n, ∀ j < n, TS i = TS j → i = j)
    (htree : ∀ k, s ≤ k → k < n → PAR k < k ∧ LAB k < 6 ∧
      TS k = letConj (letters.getD (LAB k) 0) (TS (PAR k)))
    (hclos : ∀ k < n, ∀ g < 6, TT k g < n ∧ letConj (letters.getD g 0) (TS k) = TS (TT k g))
    (hord : ∀ k, s ≤ k → k + 1 < n → PAR k * 6 + LAB k < PAR (k + 1) * 6 + LAB (k + 1))
    (hfirst : ∀ k < n, ∀ g < 6, TT k g < s ∨ PAR (TT k g) * 6 + LAB (TT k g) ≤ k * 6 + g)
    (hfuel : n ≤ fuel) :
    (gbfs key mkSeed mkNew seeds fuel).toList =
      (List.range n).map (entry mkSeed mkNew TS PAR LAB s) := by
  have hT : BfsOrder.Tree n s 6 PAR LAB TT :=
    { sn := hsn
      par := fun k hk hkn => ⟨(htree k hk hkn).1, (htree k hk hkn).2.1⟩
      same := fun k hk hkn => by
        obtain ⟨h1, h2, h3⟩ := htree k hk hkn
        obtain ⟨h4, h5⟩ := hclos (PAR k) (by omega) (LAB k) h2
        exact hdist _ h4 _ hkn (h5.symm.trans h3.symm)
      clos := fun k hk g hg => (hclos k hk g hg).1
      ord := hord
      first := hfirst }
  let E := entry mkSeed mkNew TS PAR LAB s
  have hkE : ∀ k, key (E k) = TS k := by
    intro k
    simp only [E, entry]
    split
    · exact hkS _
    · exact hkN _ _ _
  have hdistS : ∀ x, ∀ j < s, TS j = x → x ∈ seeds := by
    intro x j hj hx
    rw [← List.mem_eraseDups, hseeds, ← hx]
    exact List.mem_map_of_mem (List.mem_range.2 hj)
  let P : Array β → Prop := fun arr => arr.toList = (List.range n).map E
  let I2 : Nat → Std.HashSet (List Nat) × Array β × Nat → Prop := fun t st =>
    StInv E TS st.2.1.size st.1 st.2.1 ∧ BfsOrder.Inv n s 6 PAR LAB st.2.2 0 st.2.1.size ∧
      st.2.2 ≤ st.2.1.size ∧ (t ≤ st.2.2 ∨ st.2.2 = st.2.1.size)
  change P (gbfs key mkSeed mkNew seeds fuel)
  unfold gbfs
  refine forIn_list_bind (SeedInv mkSeed seeds) P _ seeds
    (fun k hk x st hx hI => ⟨_, ?_, seed_step hk hI⟩) _ _ (fun st hS => ?_) ⟨by simp, by simp⟩
  · rw [List.getElem?_eq_getElem hk, Option.some_inj] at hx
    subst hx
    by_cases hc : (!st.1.contains seeds[k]) = true <;> simp only [hc, ↓reduceIte] <;> rfl
  obtain ⟨hS1, hS2⟩ := hS
  rw [List.take_length] at hS1 hS2
  have hst : StInv E TS s st.1 st.2 := by
    refine ⟨?_, ?_, fun x => ?_⟩
    · have := congrArg List.length hS1
      rw [Array.length_toList, List.length_map, hseeds, List.length_map, List.length_range] at this
      exact this
    · rw [hS1, hseeds, List.map_map]
      apply List.map_congr_left
      intro k hk
      rw [List.mem_range] at hk
      simp only [Function.comp_apply, E, entry, hk, ↓reduceIte]
    · rw [hS2 x, ← List.mem_eraseDups, hseeds, List.mem_map]
      simp only [List.mem_range]
  refine BfsOrder.forIn_range_bind I2 P _ _ _ _ (fun t st2 ht hI => ?_) (fun st2 hI => ?_) ?_
  · obtain ⟨seen, arr, i⟩ := st2
    obtain ⟨hS, hI, hle, hor⟩ := hI
    dsimp only at hS hI hle hor ⊢
    split
    · rename_i hi
      have hin : i < n := by have := hI.1; omega
      have hTi : key arr[i]! = TS i := by rw [stInv_get hS hi, hkE]
      rw [hTi]
      let I3 : Nat → Std.HashSet (List Nat) × Array β → Prop := fun g st =>
        StInv E TS st.2.size st.1 st.2 ∧ BfsOrder.Inv n s 6 PAR LAB i g st.2.size ∧ i < st.2.size
      refine forIn_list_bind I3 _ _ letters (fun g hg ℓ st3 hℓ hJ => ?_) _ _ (fun st3 hJ => ?_)
        ⟨hS, hI, hi⟩
      · obtain ⟨hS3, hI3, hi3⟩ := hJ
        rw [letters_length] at hg
        have hlg : ℓ = letters.getD g 0 := by
          rw [List.getD_eq_getElem?_getD, hℓ]
          rfl
        subst hlg
        obtain ⟨htt, hcj⟩ := hclos i hin g hg
        rw [hcj]
        by_cases hold : TT i g < st3.2.size
        · have hc : st3.1.contains (TS (TT i g)) = true := (hS3.2.2 _).2 ⟨_, hold, rfl⟩
          refine ⟨(st3.1, st3.2), ?_, hS3, BfsOrder.inv_old hT hI3 hin hg hold, hi3⟩
          simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rfl
        · obtain ⟨hTm, hmn, hsm, hpar, hlab, hI'⟩ := BfsOrder.inv_new hT hI3 hin hg hold
          have hc : st3.1.contains (TS (TT i g)) = false := by
            cases e : st3.1.contains (TS (TT i g))
            · rfl
            · obtain ⟨j, hj, hx⟩ := (hS3.2.2 _).1 e
              have := hdist j (by omega) _ htt hx
              omega
          refine ⟨(st3.1.insert (TS (TT i g)), st3.2.push (mkNew (TS (TT i g)) i (letters.getD g 0))),
            ?_, ?_, ?_, ?_⟩
          · simp only [hc, Bool.not_false, ↓reduceIte]
            rfl
          · have hns : ¬ st3.2.size < s := by omega
            have hE' : mkNew (TS (TT i g)) i (letters.getD g 0) = E st3.2.size := by
              simp only [E, entry, hns, ↓reduceIte, hTm, hpar, hlab]
            dsimp only
            rw [hE', hTm, Array.size_push]
            exact stInv_push hS3
          · simpa only [Array.size_push] using hI'
          · simp only [Array.size_push]
            omega
      · obtain ⟨hS3, hI3, hi3⟩ := hJ
        rw [letters_length] at hI3
        have hti : t ≤ i := by omega
        change I2 (t + 1) (st3.1, st3.2, i + 1)
        exact ⟨hS3, BfsOrder.inv_next hI3, hi3, Or.inl (Nat.succ_le_succ hti)⟩
    · rename_i hi
      change I2 (t + 1) (seen, arr, i)
      exact ⟨hS, hI, hle, Or.inr (Nat.le_antisymm hle (Nat.le_of_not_lt hi))⟩
  · obtain ⟨seen, arr, i⟩ := st2
    obtain ⟨hS, hI, hle, hor⟩ := hI
    dsimp only at hS hI hle hor ⊢
    have hm : arr.size = n := by
      rcases hor with h | h
      · have := hI.1
        omega
      · exact BfsOrder.inv_done hT hI (by omega)
    change arr.toList = _
    rw [← hm]
    exact hS.2.1
  · have hs0 := hst.1
    have hst' : StInv E TS st.2.size st.1 st.2 := by rw [hs0]; exact hst
    have hI0 : BfsOrder.Inv n s 6 PAR LAB 0 0 st.2.size := by rw [hs0]; exact BfsOrder.inv_init hT
    exact ⟨hst', hI0, Nat.zero_le _, Or.inl (Nat.le_refl 0)⟩

end CFSG.KC.J4Q.ConjBFS

end
