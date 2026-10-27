module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {D : TabData} {elt : ℕ → Γ}

@[expose] def imageB (D : TabData) (f : ℕ → ℕ) (b : BSet) : BSet :=
  (List.range D.n).foldl (fun acc j => if b.has j then acc.set! (f j) true else acc)
    (BSet.ofFn D.n fun _ => false)

private def imageFold (D : TabData) (f : ℕ → ℕ) (b : BSet) (k : ℕ) : BSet :=
  (List.range k).foldl (fun acc j => if b.has j then acc.set! (f j) true else acc)
    (BSet.ofFn D.n fun _ => false)

private theorem has_setIfInBounds (a : BSet) (j i : ℕ) (h : j < a.size) :
    BSet.has (a.set! j true) i = true ↔ j = i ∨ BSet.has a i = true := by
  simp only [BSet.has, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases hij : j = i
  · subst i
    simp [h]
  · have hji : ¬ i = j := fun h' => hij h'.symm
    simp [hij, hji]

private theorem imageFold_succ (f : ℕ → ℕ) (b : BSet) (k : ℕ) :
    imageFold D f b (k + 1) =
      if b.has k then (imageFold D f b k).set! (f k) true else imageFold D f b k := by
  simp [imageFold, List.range_succ, List.foldl_append]

private theorem imageFold_size (f : ℕ → ℕ) (b : BSet) (k : ℕ) (hk : k ≤ D.n) :
    (imageFold D f b k).size = D.n := by
  induction k with
  | zero => simp [imageFold, BSet.size_ofFn]
  | succ k ih =>
    have hk' : k ≤ D.n := Nat.le_of_succ_le hk
    rw [imageFold_succ]
    by_cases hb : b.has k = true
    · rw [if_pos hb, Array.size_set!, ih hk']
    · rw [if_neg hb, ih hk']

private theorem imageFold_has {f : ℕ → ℕ} (hf : ∀ j < D.n, f j < D.n) (b : BSet)
    (k : ℕ) (hk : k ≤ D.n) (i : ℕ) (hi : i < D.n) :
    BSet.has (imageFold D f b k) i = true ↔ ∃ j < k, b.has j = true ∧ f j = i := by
  induction k with
  | zero =>
    simp only [imageFold, List.range_zero, List.foldl_nil]
    rw [BSet.has_ofFn _ hi]
    simp
  | succ k ih =>
    have hk' : k ≤ D.n := Nat.le_of_succ_le hk
    have hklt : k < D.n := Nat.lt_of_succ_le hk
    rw [imageFold_succ]
    by_cases hb : b.has k = true
    · rw [if_pos hb,
        has_setIfInBounds _ _ _ (by rw [imageFold_size f b k hk']; exact hf k hklt),
        ih hk']
      constructor
      · rintro (h | ⟨j, hj, hbj, hfj⟩)
        · exact ⟨k, Nat.lt_succ_self k, hb, h⟩
        · exact ⟨j, Nat.lt_succ_of_lt hj, hbj, hfj⟩
      · rintro ⟨j, hj, hbj, hfj⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact Or.inr ⟨j, hj, hbj, hfj⟩
        · exact Or.inl hfj
    · rw [if_neg hb, ih hk']
      constructor
      · rintro ⟨j, hj, hbj, hfj⟩
        exact ⟨j, Nat.lt_succ_of_lt hj, hbj, hfj⟩
      · rintro ⟨j, hj, hbj, hfj⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact ⟨j, hj, hbj, hfj⟩
        · exact absurd hbj hb

theorem has_imageB {f : ℕ → ℕ} (hf : ∀ j < D.n, f j < D.n) (b : BSet) {i : ℕ} (hi : i < D.n) :
    (imageB D f b).has i = true ↔ ∃ j < D.n, b.has j = true ∧ f j = i :=
  imageFold_has hf b D.n (le_refl D.n) i hi

theorem size_imageB (f : ℕ → ℕ) (b : BSet) : (imageB D f b).size = D.n :=
  imageFold_size f b D.n (le_refl D.n)

@[expose] def unionB (D : TabData) (b c : BSet) : BSet := BSet.ofFn D.n fun i => b.has i || c.has i

@[expose] def interB (D : TabData) (b c : BSet) : BSet :=
  BSet.ofFn D.n fun i => b.has i && c.has i

@[expose] def topB (D : TabData) : BSet := BSet.ofFn D.n fun _ => true

@[expose] def emptyB (D : TabData) : BSet := BSet.ofFn D.n fun _ => false

@[expose] def ofList (D : TabData) (l : List ℕ) : BSet := BSet.ofFn D.n fun i => l.contains i

@[expose] def members (n : ℕ) (b : BSet) : List ℕ := (List.range n).filter b.has

theorem mem_members {n : ℕ} {b : BSet} {i : ℕ} : i ∈ members n b ↔ i < n ∧ b.has i = true := by
  simp [members]

theorem rep_top (hR : Realizes D elt) : Rep D elt (topB D) (tabSet D elt) := by
  constructor
  · intro i hi
    rw [topB, BSet.has_ofFn _ hi]
    constructor
    · intro _; exact ⟨i, hi, rfl⟩
    · intro _; rfl
  · intro x hx
    exact hx

theorem rep_ofList (hR : Realizes D elt) {l : List ℕ} (hl : ∀ i ∈ l, i < D.n) :
    Rep D elt (ofList D l) {x | ∃ i ∈ l, elt i = x} := by
  constructor
  · intro i hi
    rw [ofList, BSet.has_ofFn _ hi]
    constructor
    · intro h
      exact ⟨i, List.contains_iff_mem.mp h, rfl⟩
    · rintro ⟨j, hj, hji⟩
      exact List.contains_iff_mem.mpr (hR.inj j (hl j hj) i hi hji ▸ hj)
  · rintro x ⟨i, hi, rfl⟩
    exact ⟨i, hl i hi, rfl⟩

theorem rep_inter {b c : BSet} {X Y : Set Γ} (hX : Rep D elt b X) (hY : Rep D elt c Y) :
    Rep D elt (interB D b c) (X ∩ Y) := by
  constructor
  · intro i hi
    rw [interB, BSet.has_ofFn _ hi, Bool.and_eq_true, hX.1 i hi, hY.1 i hi,
      Set.mem_inter_iff]
  · rintro x ⟨hx, _⟩
    exact hX.2 x hx

theorem rep_union {b c : BSet} {X Y : Set Γ} (hX : Rep D elt b X) (hY : Rep D elt c Y) :
    Rep D elt (unionB D b c) (X ∪ Y) := by
  constructor
  · intro i hi
    rw [unionB, BSet.has_ofFn _ hi, Bool.or_eq_true, hX.1 i hi, hY.1 i hi,
      Set.mem_union]
  · rintro x (hx | hx)
    · exact hX.2 x hx
    · exact hY.2 x hx

theorem rep_image (hR : Realizes D elt) {f : ℕ → ℕ} (hf : ∀ j < D.n, f j < D.n) {g : Γ → Γ}
    (hfg : ∀ j < D.n, elt (f j) = g (elt j)) {b : BSet} {X : Set Γ} (hX : Rep D elt b X) :
    Rep D elt (imageB D f b) (g '' X) := by
  constructor
  · intro i hi
    rw [has_imageB hf b hi]
    constructor
    · rintro ⟨j, hj, hbj, hfji⟩
      exact ⟨elt j, (hX.1 j hj).1 hbj, by rw [← hfg j hj, hfji]⟩
    · rintro ⟨x, hx, hgx⟩
      obtain ⟨j, hj, hjx⟩ := hX.2 x hx
      refine ⟨j, hj, (hX.1 j hj).2 (hjx ▸ hx), ?_⟩
      exact hR.inj (f j) (hf j hj) i hi (by rw [hfg j hj, hjx, hgx])
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hjx⟩ := hX.2 x hx
    exact ⟨f j, hf j hj, by rw [hfg j hj, hjx]⟩

theorem Rep.subgroup_eq {b : BSet} {X Y : Subgroup Γ} (hX : Rep D elt b (X : Set Γ))
    (hY : Rep D elt b (Y : Set Γ)) : X = Y :=
  SetLike.coe_injective (hX.unique hY)

theorem Rep.card_set (hR : Realizes D elt) {b : BSet} {X : Set Γ} (hX : Rep D elt b X) :
    Nat.card X = BSet.count D.n b := by
  let Y : Set ℕ := {i | i ∈ members D.n b}
  let f : Y → X := fun i =>
    ⟨elt i.1, (hX.1 i.1 (mem_members.mp i.2).1).1 (mem_members.mp i.2).2⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact hR.inj a.1 (mem_members.mp a.2).1 b.1 (mem_members.mp b.2).1
      (congrArg Subtype.val hab)
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨i, hi, hix⟩ := hX.2 x.1 x.2
    refine ⟨⟨i, ?_⟩, Subtype.ext hix⟩
    exact mem_members.mpr ⟨hi, (hX.1 i hi).2 (hix ▸ x.2)⟩
  have hYX : Nat.card X = Nat.card Y :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
  have hcard : Nat.card Y = (members D.n b).toFinset.card :=
    Nat.subtype_card (members D.n b).toFinset (fun i => List.mem_toFinset)
  rw [hYX, hcard]
  simp only [members]
  rw [List.toFinset_card_of_nodup ((List.nodup_range (n := D.n)).filter b.has)]
  simp [BSet.count, List.countP_eq_length_filter]

theorem Rep.card_subgroup (hR : Realizes D elt) {b : BSet} {X : Subgroup Γ}
    (hX : Rep D elt b (X : Set Γ)) : Nat.card X = BSet.count D.n b :=
  hX.card_set hR

theorem Rep.subset_iff {b c : BSet} {X Y : Set Γ} (hX : Rep D elt b X) (hY : Rep D elt c Y) :
    X ⊆ Y ↔ ∀ i < D.n, b.has i = true → c.has i = true := by
  constructor
  · intro hsub i hi hb
    exact (hY.1 i hi).2 (hsub ((hX.1 i hi).1 hb))
  · intro h x hx
    obtain ⟨i, hi, hix⟩ := hX.2 x hx
    have hbi : b.has i = true := (hX.1 i hi).2 (hix.symm ▸ hx)
    exact hix ▸ (hY.1 i hi).1 (h i hi hbi)

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
