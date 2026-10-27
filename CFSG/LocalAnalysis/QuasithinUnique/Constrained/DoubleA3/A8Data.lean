module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A8Fix

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Equiv Equiv.Perm Subgroup

@[expose] def mk8 (f g : Fin 8 → Fin 8) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) :
    Perm (Fin 8) :=
  ⟨f, g, h1, h2⟩

@[expose] def dd : Fin 8 → Perm (Fin 8) :=
  ![mk8 ![0, 1, 2, 3, 4, 5, 6, 7] ![0, 1, 2, 3, 4, 5, 6, 7] (by decide) (by decide),
    mk8 ![0, 1, 3, 4, 5, 2, 7, 6] ![0, 1, 5, 2, 3, 4, 7, 6] (by decide) (by decide),
    mk8 ![0, 1, 4, 5, 2, 3, 6, 7] ![0, 1, 4, 5, 2, 3, 6, 7] (by decide) (by decide),
    mk8 ![0, 1, 5, 2, 3, 4, 7, 6] ![0, 1, 3, 4, 5, 2, 7, 6] (by decide) (by decide),
    mk8 ![0, 1, 5, 4, 3, 2, 6, 7] ![0, 1, 5, 4, 3, 2, 6, 7] (by decide) (by decide),
    mk8 ![0, 1, 2, 5, 4, 3, 7, 6] ![0, 1, 2, 5, 4, 3, 7, 6] (by decide) (by decide),
    mk8 ![0, 1, 3, 2, 5, 4, 6, 7] ![0, 1, 3, 2, 5, 4, 6, 7] (by decide) (by decide),
    mk8 ![0, 1, 4, 3, 2, 5, 7, 6] ![0, 1, 4, 3, 2, 5, 7, 6] (by decide) (by decide)]

@[expose] def mt : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 2, 3, 0, 5, 6, 7, 4], ![2, 3, 0, 1, 6, 7, 4, 5],
    ![3, 0, 1, 2, 7, 4, 5, 6], ![4, 7, 6, 5, 0, 3, 2, 1], ![5, 4, 7, 6, 1, 0, 3, 2],
    ![6, 5, 4, 7, 2, 1, 0, 3], ![7, 6, 5, 4, 3, 2, 1, 0]]

@[expose] def iv : Fin 8 → Fin 8 := ![0, 3, 2, 1, 4, 5, 6, 7]

theorem dd_zero : dd 0 = 1 := by decide +kernel

theorem dd_mul : ∀ i j : Fin 8, dd i * dd j = dd (mt i j) := by decide +kernel

theorem dd_inv : ∀ i : Fin 8, (dd i)⁻¹ = dd (iv i) := by decide +kernel

theorem dd_inj : Function.Injective dd := by
  have h : ∀ i j : Fin 8, dd i = dd j → i = j := by decide +kernel
  exact fun i j hij => h i j hij

theorem dd_fix : ∀ i : Fin 8, dd i 0 = 0 ∧ dd i 1 = 1 := by decide +kernel

theorem dd_even : ∀ i : Fin 8, sign (dd i) = 1 := by decide +kernel

theorem klein_index : ∀ I : Finset (Fin 8), I.card = 4 → (∀ i ∈ I, mt i i = 0) →
    (∀ i ∈ I, ∀ j ∈ I, mt i j ∈ I) → I = {0, 2, 4, 6} ∨ I = {0, 2, 5, 7} := by decide +kernel

theorem ia_fix : ∀ x : Fin 8, (∀ i ∈ ({0, 2, 4, 6} : Finset (Fin 8)), dd i x = x) ↔
    x ∈ ({0, 1, 6, 7} : Finset (Fin 8)) := by decide +kernel

@[expose] def permPi : Perm (Fin 8) :=
  mk8 ![2, 3, 0, 1, 6, 7, 4, 5] ![2, 3, 0, 1, 6, 7, 4, 5] (by decide) (by decide)

theorem permPi_inv : ∀ x ∈ ({2, 3, 4, 5} : Finset (Fin 8)),
    permPi⁻¹ x ∈ ({0, 1, 6, 7} : Finset (Fin 8)) := by decide +kernel

@[expose] def d0 : Subgroup (Perm (Fin 8)) where
  carrier := Set.range dd
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨mt i j, (dd_mul i j).symm⟩
  one_mem' := ⟨0, dd_zero⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨iv i, (dd_inv i).symm⟩

theorem card_d0 : Nat.card d0 = 8 := by
  have h : Nat.card (Set.range dd) = Nat.card (Fin 8) := Nat.card_range_of_injective dd_inj
  rw [Nat.card_fin] at h
  exact h

theorem d0_le_fixerAlt : d0 ≤ fixerAlt {0, 1} := by
  rintro _ ⟨i, rfl⟩
  refine mem_fixerAlt.mpr ⟨fun y hy => ?_, dd_even i⟩
  obtain ⟨h0, h1⟩ := dd_fix i
  obtain rfl | rfl : y = 0 ∨ y = 1 := by simpa using hy
  · exact h0
  · exact h1

theorem klein_in_d0 {W : Subgroup (Perm (Fin 8))} (hW : W ≤ d0) (hc : Nat.card W = 4)
    (hsq : ∀ u ∈ W, u * u = 1) :
    (∀ x, x ∈ W ↔ ∃ i ∈ ({0, 2, 4, 6} : Finset (Fin 8)), dd i = x) ∨
      (∀ x, x ∈ W ↔ ∃ i ∈ ({0, 2, 5, 7} : Finset (Fin 8)), dd i = x) := by
  classical
  set I : Finset (Fin 8) := Finset.univ.filter (fun i => dd i ∈ W) with hI
  have hmemI : ∀ i, i ∈ I ↔ dd i ∈ W := by
    intro i
    simp [hI]
  have hxW : ∀ x, x ∈ W ↔ ∃ i ∈ I, dd i = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, rfl⟩ := hW hx
      exact ⟨i, (hmemI i).mpr hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact (hmemI i).mp hi
  have hIcard : I.card = 4 := by
    let f : {i // i ∈ I} → W := fun i => ⟨dd i.1, (hmemI i.1).mp i.2⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j hij
        exact Subtype.ext (dd_inj (congrArg Subtype.val hij))
      · rintro ⟨x, hx⟩
        obtain ⟨i, hi, rfl⟩ := (hxW x).mp hx
        exact ⟨⟨i, hi⟩, rfl⟩
    rw [← hc, ← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
      Fintype.card_coe]
  have hIsq : ∀ i ∈ I, mt i i = 0 := by
    intro i hi
    have h1 := hsq _ ((hmemI i).mp hi)
    rw [dd_mul, ← dd_zero] at h1
    exact dd_inj h1
  have hImul : ∀ i ∈ I, ∀ j ∈ I, mt i j ∈ I := by
    intro i hi j hj
    rw [hmemI, ← dd_mul]
    exact W.mul_mem ((hmemI i).mp hi) ((hmemI j).mp hj)
  rcases klein_index I hIcard hIsq hImul with h | h
  · left
    intro x
    rw [hxW, h]
  · right
    intro x
    rw [hxW, h]

end CFSG.QuasithinUnique.DoubleA3
