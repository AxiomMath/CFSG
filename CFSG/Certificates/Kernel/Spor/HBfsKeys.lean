module

public import CFSG.Certificates.Kernel.Spor.HBfsClosed
public import CFSG.Certificates.Kernel.Spor.HBfsTree
public import CFSG.Certificates.Kernel.Spor.MulHSound

public section

namespace CFSG.KS.HBfs

open CFSG.KS.KeyBfs (forIn_range'_done)

section

variable {α : Type} [Inhabited α] {key : α → UInt64} {k : Nat} {st : Nat → α → α} {root : α}

theorem hcinv_final (cap : Nat) :
    ∃ h, (h = (Id.run (forIn (List.range' 0 cap) (hInit key root) (hOuter key st k))).2.1.size ∨
      cap ≤ h) ∧
      HCInv key k st root (fun _ => True) h 0
        (Id.run (forIn (List.range' 0 cap) (hInit key root) (hOuter key st k))) := by
  refine forIn_range'_done cap 0 (hInit key root) (hOuter key st k)
    (fun h s => h ≤ s.2.1.size ∧ HCInv key k st root (fun _ => True) h 0 s)
    (fun s => ∃ h, (h = s.2.1.size ∨ cap ≤ h) ∧ HCInv key k st root (fun _ => True) h 0 s)
    (fun h _ s hP => ?_) (fun s hP => ⟨cap, Or.inr (Nat.le_refl _), hP.2⟩)
    ⟨Nat.zero_le _, hcinv_init trivial⟩
  obtain ⟨hhs, hI⟩ := hP
  rw [Nat.zero_add]
  rcases Nat.lt_or_ge h s.2.1.size with a | a
  · obtain ⟨hI', hle⟩ := hcinv_inner (fun _ _ _ _ => trivial) hI a
    exact Or.inl ⟨_, by simp [hOuter, a], by omega, hI'⟩
  · have e : h = s.2.1.size := by omega
    have hns : ¬ h < s.2.1.size := by omega
    exact Or.inr ⟨s, by simp [hOuter, hns], h, Or.inl e, hI⟩

theorem hbfs_keys (key : α → UInt64) (st : Nat → α → α) (k : Nat) (root : α) (cap : Nat) :
    (∀ a < (hbfs key st k root cap).1.size, ∀ b < (hbfs key st k root cap).1.size,
      key (hbfs key st k root cap).1[a]! = key (hbfs key st k root cap).1[b]! → a = b) ∧
    ∀ i < (hbfs key st k root cap).1.size, i < cap → ∀ l < k,
      ∃ q < (hbfs key st k root cap).1.size,
        key (st l (hbfs key st k root cap).1[i]!) = key (hbfs key st k root cap).1[q]! := by
  obtain ⟨h, hh, hI⟩ := hcinv_final (key := key) (st := st) (k := k) (root := root) cap
  rw [hbfs_eq]
  generalize Id.run (forIn (List.range' 0 cap) (hInit key root) (hOuter key st k)) = s at hh hI
  obtain ⟨-, -, -, -, -, a6, -, -, a9⟩ := hI
  refine ⟨a6, fun i hi hc l hl => a9 i hi l hl (Or.inl ?_)⟩
  change i < s.2.1.size at hi
  rcases hh with e | e <;> omega

theorem length_le_of_keys {β : Type} [DecidableEq β] {key : α → β} {E : Array α} {L : List β}
    (hL : L.Nodup)
    (hm : ∀ x ∈ L, ∃ q < E.size, x = key E[q]!) : L.length ≤ E.size := by
  have h1 : L.toFinset ⊆ (Finset.range E.size).image fun q => key E[q]! := by
    intro x hx
    obtain ⟨q, hq, e⟩ := hm x (List.mem_toFinset.1 hx)
    exact Finset.mem_image.2 ⟨q, Finset.mem_range.2 hq, e.symm⟩
  have h2 := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hL] at h2
  exact h2.trans (Finset.card_image_le.trans (by simp))

@[expose] def FiveTree {β : Type} (key : α → β) (st : Nat → α → α) (k : Nat) : Nat → List α → Prop
  | 0, Kn => ∃ Xs : List α, (∀ X ∈ Xs, X ∈ Kn ∨ ∃ Y ∈ Kn, ∃ l < k, X = st l Y) ∧
      (Xs.map key).Nodup ∧ 5 ≤ Xs.length
  | f + 1, Kn => FiveTree key st k 0 Kn ∨
      ((∃ Y ∈ Kn, ∃ l < k, key (st l Y) ∉ Kn.map key) ∧
        ∀ Y ∈ Kn, ∀ l < k, key (st l Y) ∉ Kn.map key → FiveTree key st k f (Kn ++ [st l Y]))

theorem five_leaf {E : Array α} {cap j : Nat} (hj : j ≤ E.size) (hsc : E.size < cap)
    (hcl : ∀ i < E.size, i < cap → ∀ l < k, ∃ q < E.size, key (st l E[i]!) = key E[q]!)
    (h : FiveTree key st k 0 ((List.range j).map fun i => E[i]!)) : 5 ≤ E.size := by
  rw [FiveTree.eq_1] at h
  obtain ⟨Xs, hX, hd, h5⟩ := h
  refine h5.trans ((List.length_map (f := key)).symm.le.trans
    (length_le_of_keys (key := key) hd ?_))
  intro x hx
  obtain ⟨X, hX', rfl⟩ := List.mem_map.1 hx
  rcases hX X hX' with hm | ⟨Y, hY, l, hl, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hm
    exact ⟨i, by have := List.mem_range.1 hi; omega, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hY
    have hi' := List.mem_range.1 hi
    exact hcl i (by omega) (by omega) l hl

theorem five_of_tree_aux {E : Array α} {par lab : Array Nat} {cap : Nat} (hs : E.size < 5)
    (hcap : 5 ≤ cap)
    (hinj : ∀ a < E.size, ∀ b < E.size, key E[a]! = key E[b]! → a = b)
    (hcl : ∀ i < E.size, i < cap → ∀ l < k, ∃ q < E.size, key (st l E[i]!) = key E[q]!)
    (htr : ∀ i, 0 < i → i < E.size → par[i]! < i ∧ lab[i]! < k ∧ E[i]! = st lab[i]! E[par[i]!]!) :
    ∀ f j, 0 < j → j ≤ E.size → ¬ FiveTree key st k f ((List.range j).map fun i => E[i]!) := by
  intro f
  induction f with
  | zero =>
    intro j _ hj h
    have := five_leaf hj (by omega) hcl h
    omega
  | succ f ih =>
    intro j hj0 hj h
    rw [FiveTree.eq_2] at h
    rcases h with h | ⟨⟨Y, hY, l, hl, hnew⟩, hall⟩
    · have := five_leaf hj (by omega) hcl h
      omega
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hY
    have hi' := List.mem_range.1 hi
    obtain ⟨q, hq, e⟩ := hcl i (by omega) (by omega) l hl
    have hjq : j ≤ q := by
      by_contra hc
      exact hnew (e ▸ List.mem_map.2 ⟨E[q]!, List.mem_map.2 ⟨q, List.mem_range.2 (by omega), rfl⟩,
        rfl⟩)
    have hjs : j < E.size := by omega
    obtain ⟨t1, t2, t3⟩ := htr j hj0 hjs
    have hmem : E[par[j]!]! ∈ (List.range j).map fun i => E[i]! :=
      List.mem_map.2 ⟨_, List.mem_range.2 t1, rfl⟩
    have hnew' : key (st lab[j]! E[par[j]!]!) ∉ ((List.range j).map fun i => E[i]!).map key := by
      intro hm
      obtain ⟨X, hX, eX⟩ := List.mem_map.1 hm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hX
      have ha' := List.mem_range.1 ha
      rw [← t3] at eX
      exact absurd (hinj a (by omega) j hjs eX) (by omega)
    have h' := hall _ hmem _ t2 hnew'
    rw [← t3] at h'
    have e2 : ((List.range j).map fun i => E[i]!) ++ [E[j]!] =
        (List.range (j + 1)).map fun i => E[i]! := by
      rw [List.range_succ, List.map_append]
      rfl
    rw [e2] at h'
    exact ih (j + 1) (by omega) (by omega) h'

theorem five_of_tree {cap f : Nat} (hcap : 5 ≤ cap) (h : FiveTree key st k f [root]) :
    5 ≤ (hbfs key st k root cap).1.size := by
  obtain ⟨hpos, hr, -, -, htr⟩ := hbfs_tree key st k root cap
  obtain ⟨hinj, hcl⟩ := hbfs_keys key st k root cap
  by_contra hs
  refine five_of_tree_aux (by omega) hcap hinj hcl htr f 1 Nat.one_pos hpos ?_
  simpa [hr] using h

theorem FiveTree.map {α' β β' : Type} {keyA : α' → β'} {stA : Nat → α' → α'} {Good : α' → Prop}
    {key' : α → β} {g : β → β'} (hg : Function.Injective g) (φ : α' → α)
    (hst : ∀ l < k, ∀ x, Good x → Good (stA l x) ∧ φ (stA l x) = st l (φ x))
    (hkey : ∀ x, Good x → g (key' (φ x)) = keyA x) :
    ∀ f (Kn : List α'), (∀ x ∈ Kn, Good x) → FiveTree keyA stA k f Kn →
      FiveTree key' st k f (Kn.map φ) := by
  have leaf : ∀ Kn : List α', (∀ x ∈ Kn, Good x) → FiveTree keyA stA k 0 Kn →
      FiveTree key' st k 0 (Kn.map φ) := by
    intro Kn hG h
    rw [FiveTree.eq_1] at h ⊢
    obtain ⟨Xs, hX, hd, h5⟩ := h
    have hXG : ∀ X ∈ Xs, Good X := by
      intro X hX'
      rcases hX X hX' with hm | ⟨Y, hY, l, hl, rfl⟩
      · exact hG X hm
      · exact (hst l hl Y (hG Y hY)).1
    refine ⟨Xs.map φ, fun Z hZ => ?_, ?_, by simpa using h5⟩
    · obtain ⟨X, hX', rfl⟩ := List.mem_map.1 hZ
      rcases hX X hX' with hm | ⟨Y, hY, l, hl, rfl⟩
      · exact Or.inl (List.mem_map.2 ⟨X, hm, rfl⟩)
      · exact Or.inr ⟨φ Y, List.mem_map.2 ⟨Y, hY, rfl⟩, l, hl, (hst l hl Y (hG Y hY)).2⟩
    · refine List.Nodup.of_map g ?_
      rw [List.map_map, List.map_map]
      have e : Xs.map ((g ∘ key') ∘ φ) = Xs.map keyA :=
        List.map_congr_left fun X hX' => hkey X (hXG X hX')
      rw [e]
      exact hd
  intro f
  induction f with
  | zero => exact leaf
  | succ f ih =>
    intro Kn hG h
    rw [FiveTree.eq_2] at h ⊢
    rcases h with h | ⟨⟨Y, hY, l, hl, hnew⟩, hall⟩
    · exact Or.inl (leaf Kn hG h)
    have hmem : ∀ x, Good x → (key' (φ x) ∈ (Kn.map φ).map key' ↔ keyA x ∈ Kn.map keyA) := by
      intro x hx
      rw [List.map_map]
      constructor
      · intro hm
        obtain ⟨Z, hZ, e⟩ := List.mem_map.1 hm
        refine List.mem_map.2 ⟨Z, hZ, ?_⟩
        rw [← hkey Z (hG Z hZ), ← hkey x hx]
        exact congrArg g e
      · intro hm
        obtain ⟨Z, hZ, e⟩ := List.mem_map.1 hm
        refine List.mem_map.2 ⟨Z, hZ, hg ?_⟩
        rw [Function.comp_apply, hkey Z (hG Z hZ), hkey x hx]
        exact e
    refine Or.inr ⟨⟨φ Y, List.mem_map.2 ⟨Y, hY, rfl⟩, l, hl, ?_⟩, ?_⟩
    · rw [← (hst l hl Y (hG Y hY)).2, hmem _ (hst l hl Y (hG Y hY)).1]
      exact hnew
    · intro Y' hY' l' hl' hn'
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY'
      obtain ⟨hGs, e⟩ := hst l' hl' Z (hG Z hZ)
      rw [← e, hmem _ hGs] at hn'
      have := ih (Kn ++ [stA l' Z]) (fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hG x hx
        · rw [List.mem_singleton.1 hx]
          exact hGs) (hall Z hZ l' hl' hn')
      rw [List.map_append, List.map_singleton, e] at this
      exact this

end

end CFSG.KS.HBfs

namespace CFSG.KS.MulH

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem conjClosureH_eq (n : Nat) (gens gensInv : Array Table) (x : Table) (cap : Nat) :
    conjClosureH n gens gensInv x cap = CFSG.KS.HBfs.hbfs (hkey n)
      (fun l y => conjT n gens[l]! gensInv[l]! y) gens.size x cap := rfl

theorem ofFn_getElem! {β : Type} [Inhabited β] (E : Array β) :
    (Array.ofFn (n := E.size) fun i => E[i.val]!) = E := by
  apply Array.ext (by simp)
  intro i h1 h2
  rw [Array.getElem_ofFn, getElem!_pos E i h2]

theorem conjTree_keys (n : Nat) (gens gensInv : Array Table) (x : Table) (cap : Nat) :
    conjTreeOK n gens gensInv x (conjClosureH n gens gensInv x cap).1
      (conjClosureH n gens gensInv x cap).2.1 (conjClosureH n gens gensInv x cap).2.2 = true ∧
    hkeysDistinct n (conjClosureH n gens gensInv x cap).1.toList = true := by
  rw [conjClosureH_eq]
  obtain ⟨hpos, hr, hp, hl, htr⟩ := CFSG.KS.HBfs.hbfs_tree (hkey n)
    (fun l y => conjT n gens[l]! gensInv[l]! y) gens.size x cap
  obtain ⟨hinj, -⟩ := CFSG.KS.HBfs.hbfs_keys (hkey n)
    (fun l y => conjT n gens[l]! gensInv[l]! y) gens.size x cap
  generalize CFSG.KS.HBfs.hbfs (hkey n) (fun l y => conjT n gens[l]! gensInv[l]! y) gens.size x
    cap = R at hpos hr hp hl htr hinj
  refine ⟨?_, ?_⟩
  · unfold conjTreeOK
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hpos, by rw [hr]; exact tblEqH_self n x⟩, allInH_of fun i h1 h2 => ?_⟩
    obtain ⟨a1, a2, a3⟩ := htr i (by omega) h2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨a1, a2⟩, ?_⟩
    rw [a3]
    exact tblEqH_self n _
  · rw [← ofFn_getElem! R.1]
    exact hkeysDistinct_ofFn fun a ha b hb e => hinj a ha b hb (UInt64.toNat_inj.1 e)

end CFSG.KS.MulH

end
