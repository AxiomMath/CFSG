module

public import Mathlib.GroupTheory.Perm.Sign

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

namespace PairFlip

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def J0 (ι : Type*) : Subgroup (Perm (ι × Bool)) where
  carrier := {w | ∀ z, w z = z ∨ w z = (z.1, !z.2)}
  mul_mem' := by
    intro a b ha hb z
    simp only [Perm.mul_apply]
    rcases hb z with e | e
    · rw [e]; exact ha z
    · rw [e]
      rcases ha (z.1, !z.2) with e' | e'
      · right; exact e'
      · left; rw [e']; simp
  one_mem' := fun z => Or.inl rfl
  inv_mem' := by
    intro a ha z
    have h := ha (a⁻¹ z)
    have hz : a (a⁻¹ z) = z := by simp
    rw [hz] at h
    generalize a⁻¹ z = y at h ⊢
    obtain ⟨y1, y2⟩ := y
    rcases h with e | e
    · left; exact e.symm
    · right
      rw [e]
      simp

omit [Fintype ι] [DecidableEq ι] in
theorem mem_J0 {w : Perm (ι × Bool)} : w ∈ J0 ι ↔ ∀ z, w z = z ∨ w z = (z.1, !z.2) := Iff.rfl

@[expose] def tp (i : ι) : Perm (ι × Bool) := swap (i, true) (i, false)

theorem tp_apply (i j : ι) (b : Bool) : tp i (j, b) = if j = i then (i, !b) else (j, b) := by
  unfold tp
  by_cases hji : j = i
  · subst hji
    cases b <;> simp
  · simp only [hji, ↓reduceIte]
    apply swap_apply_of_ne_of_ne
    · intro h; exact hji (congrArg Prod.fst h)
    · intro h; exact hji (congrArg Prod.fst h)

theorem tp_mem_J0 (i : ι) : tp i ∈ J0 ι := by
  intro z
  rcases z with ⟨j, b⟩
  rw [tp_apply]
  by_cases hji : j = i
  · subst hji; simp
  · simp [hji]

theorem tp_mul_tp_self (i : ι) : tp i * tp i = 1 := by
  unfold tp; exact swap_mul_self _ _

theorem sign_tp (i : ι) : sign (tp i) = -1 := by
  unfold tp; exact sign_swap (by simp)

@[expose] def flipSet (w : Perm (ι × Bool)) : Finset ι :=
  Finset.univ.filter fun i => w (i, true) ≠ (i, true)

theorem mem_flipSet {w : Perm (ι × Bool)} {i : ι} : i ∈ flipSet w ↔ w (i, true) ≠ (i, true) := by
  simp [flipSet]

theorem J0_apply {w : Perm (ι × Bool)} (hw : w ∈ J0 ι) (i : ι) (b : Bool) :
    w (i, b) = if i ∈ flipSet w then (i, !b) else (i, b) := by
  by_cases h : w (i, true) = (i, true)
  · have hi : i ∉ flipSet w := by rw [mem_flipSet]; exact not_not.2 h
    simp only [hi, ↓reduceIte]
    cases b
    · rcases hw (i, false) with e | e
      · exact e
      · exfalso
        have : w (i, false) = w (i, true) := by rw [e, h]; rfl
        have := w.injective this
        simp at this
    · exact h
  · have hi : i ∈ flipSet w := mem_flipSet.2 h
    simp only [hi, ↓reduceIte]
    have h1 : w (i, true) = (i, false) := by
      rcases hw (i, true) with e | e
      · exact absurd e h
      · simpa using e
    cases b
    · rcases hw (i, false) with e | e
      · exfalso
        have : w (i, false) = w (i, true) := by rw [e, h1]
        have := w.injective this
        simp at this
      · simpa using e
    · simpa using h1

theorem eq_one_of_flipSet_eq_empty {w : Perm (ι × Bool)} (hw : w ∈ J0 ι) (h : flipSet w = ∅) :
    w = 1 := by
  apply Equiv.ext
  rintro ⟨i, b⟩
  rw [J0_apply hw, h]
  simp

theorem mem_flipSet_tp_mul {w : Perm (ι × Bool)} (hw : w ∈ J0 ι) (i j : ι) :
    j ∈ flipSet (tp i * w) ↔ (j ∈ flipSet w ↔ j ≠ i) := by
  rw [mem_flipSet, Perm.mul_apply, J0_apply hw]
  by_cases hj : j ∈ flipSet w
  · simp only [hj, ↓reduceIte, Bool.not_true]; rw [tp_apply]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  · simp only [hj, ↓reduceIte]; rw [tp_apply]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]

theorem flipSet_tp_mul_of_mem {w : Perm (ι × Bool)} (hw : w ∈ J0 ι) {i : ι} (hi : i ∈ flipSet w) :
    flipSet (tp i * w) = (flipSet w).erase i := by
  ext j
  rw [mem_flipSet_tp_mul hw, Finset.mem_erase]
  by_cases hji : j = i
  · subst hji; simp [hi]
  · simp [hji]

theorem tp_mul_mem_J0 {w : Perm (ι × Bool)} (hw : w ∈ J0 ι) (i : ι) : tp i * w ∈ J0 ι :=
  mul_mem (tp_mem_J0 i) hw

theorem sign_eq_of_J0 : ∀ (n : ℕ) (w : Perm (ι × Bool)), w ∈ J0 ι → (flipSet w).card = n →
    sign w = (-1) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw hn
    by_cases h0 : flipSet w = ∅
    · have : w = 1 := eq_one_of_flipSet_eq_empty hw h0
      rw [h0] at hn
      simp at hn
      subst hn
      simp [this]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 h0
      have hw' := tp_mul_mem_J0 hw i
      have hcard : (flipSet (tp i * w)).card = n - 1 := by
        rw [flipSet_tp_mul_of_mem hw hi, Finset.card_erase_of_mem hi, hn]
      have hn1 : 0 < n := by rw [← hn]; exact Finset.card_pos.2 ⟨i, hi⟩
      have h1 := ih (n - 1) (by omega) _ hw' hcard
      rw [map_mul, sign_tp] at h1
      have h2 : sign w = -((-1) ^ (n - 1)) := by
        have : (-1 : ℤˣ) * sign w = (-1) ^ (n - 1) := h1
        calc sign w = -((-1 : ℤˣ) * sign w) := by simp
          _ = _ := by rw [this]
      rw [h2]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [pow_succ]

theorem even_card_flipSet_of_sign {w : Perm (ι × Bool)} (hw : w ∈ J0 ι) (h : sign w = 1) :
    Even (flipSet w).card := by
  have := sign_eq_of_J0 _ w hw rfl
  rw [h] at this
  exact (neg_one_pow_eq_one_iff_even (by decide)).1 this.symm

theorem mem_of_even_flipSet {W : Subgroup (Perm (ι × Bool))} {T : Finset ι}
    (hI : ∀ i, i ∉ T → tp i ∈ W) (hT : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → tp i * tp j ∈ W) :
    ∀ (n : ℕ) (c : Perm (ι × Bool)), c ∈ J0 ι → (flipSet c).card = n →
      Even (flipSet c ∩ T).card → c ∈ W := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc hn hev
    by_cases h0 : flipSet c = ∅
    · rw [eq_one_of_flipSet_eq_empty hc h0]; exact W.one_mem
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 h0
      by_cases hiT : i ∈ T
      ·
        have hmem : i ∈ flipSet c ∩ T := Finset.mem_inter.2 ⟨hi, hiT⟩
        have hgt : 1 < (flipSet c ∩ T).card := by
          have hpos : 0 < (flipSet c ∩ T).card := Finset.card_pos.2 ⟨i, hmem⟩
          obtain ⟨k, hk⟩ := hev
          omega
        obtain ⟨j, hjm, hji⟩ := Finset.exists_mem_ne hgt i
        have hj : j ∈ flipSet c := (Finset.mem_inter.1 hjm).1
        have hjT : j ∈ T := (Finset.mem_inter.1 hjm).2
        have hc1 := tp_mul_mem_J0 hc j
        have hset1 : flipSet (tp j * c) = (flipSet c).erase j := flipSet_tp_mul_of_mem hc hj
        have hi1 : i ∈ flipSet (tp j * c) := by
          rw [hset1]; exact Finset.mem_erase.2 ⟨hji.symm, hi⟩
        have hc2 := tp_mul_mem_J0 hc1 i
        have hset2 : flipSet (tp i * (tp j * c)) = ((flipSet c).erase j).erase i := by
          rw [flipSet_tp_mul_of_mem hc1 hi1, hset1]
        have hcard2 : (flipSet (tp i * (tp j * c))).card = n - 2 := by
          rw [hset2, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hji.symm, hi⟩),
            Finset.card_erase_of_mem hj, hn]
          omega
        have hn2 : 2 ≤ n := by
          have : 2 ≤ (flipSet c).card := by
            have h1 : (flipSet c ∩ T).card ≤ (flipSet c).card := Finset.card_le_card Finset.inter_subset_left
            omega
          omega
        have hpar : Even (flipSet (tp i * (tp j * c)) ∩ T).card := by
          rw [hset2]
          have : ((flipSet c).erase j).erase i ∩ T = ((flipSet c ∩ T).erase j).erase i := by
            ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto
          rw [this, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hji.symm, hmem⟩),
            Finset.card_erase_of_mem hjm]
          obtain ⟨k, hk⟩ := hev
          exact ⟨k - 1, by omega⟩
        have h2 := ih (n - 2) (by omega) _ hc2 hcard2 hpar
        have hprod : tp i * tp j ∈ W := hT i hiT j hjT hji.symm
        have : c = (tp i * tp j)⁻¹ * (tp i * (tp j * c)) := by
          simp [mul_assoc]
        rw [this]
        exact W.mul_mem (W.inv_mem hprod) h2
      · have hIi : tp i ∈ W := hI i hiT
        have hc1 := tp_mul_mem_J0 hc i
        have hset1 : flipSet (tp i * c) = (flipSet c).erase i := flipSet_tp_mul_of_mem hc hi
        have hcard1 : (flipSet (tp i * c)).card = n - 1 := by
          rw [hset1, Finset.card_erase_of_mem hi, hn]
        have hn1 : 0 < n := by rw [← hn]; exact Finset.card_pos.2 ⟨i, hi⟩
        have hpar : Even (flipSet (tp i * c) ∩ T).card := by
          rw [hset1]
          have : (flipSet c).erase i ∩ T = flipSet c ∩ T := by
            ext x; simp only [Finset.mem_inter, Finset.mem_erase]
            constructor
            · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
            · rintro ⟨h, h'⟩; exact ⟨⟨fun hx => hiT (hx ▸ h'), h⟩, h'⟩
          rw [this]; exact hev
        have h1 := ih (n - 1) (by omega) _ hc1 hcard1 hpar
        have : c = tp i * (tp i * c) := by simp [← mul_assoc, tp_mul_tp_self]
        rw [this]
        exact W.mul_mem hIi h1

end PairFlip

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
