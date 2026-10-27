module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core

open Equiv

@[expose] def aA6Perm : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def bA6Perm : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def aA6 : alternatingGroup (Fin 6) :=
  ⟨aA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

@[expose] def bA6 : alternatingGroup (Fin 6) :=
  ⟨bA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

theorem aA6_pow_three : aA6 ^ 3 = 1 :=
  Subtype.ext (by
    show aA6Perm ^ 3 = 1
    decide +kernel)

theorem bA6_pow_three : bA6 ^ 3 = 1 :=
  Subtype.ext (by
    show bA6Perm ^ 3 = 1
    decide +kernel)

theorem commute_aA6_bA6 : Commute aA6 bA6 := by
  show aA6 * bA6 = bA6 * aA6
  exact Subtype.ext (by
    show aA6Perm * bA6Perm = bA6Perm * aA6Perm
    decide +kernel)

theorem aA6_ne_one : aA6 ≠ 1 := by
  decide +kernel

private def cBA6Perm : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 5 2 * Equiv.swap 2 4

theorem isConj_bA6_aA6 : IsConj bA6 aA6 := by
  refine isConj_iff.mpr
    ⟨⟨cBA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩, ?_⟩
  apply Subtype.ext
  show cBA6Perm * bA6Perm * cBA6Perm⁻¹ = aA6Perm
  decide +kernel

private def cInvA6Perm : Equiv.Perm (Fin 6) := Equiv.swap 1 2 * Equiv.swap 4 5

theorem isConj_aA6_inv : IsConj aA6 aA6⁻¹ := by
  refine isConj_iff.mpr
    ⟨⟨cInvA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩, ?_⟩
  apply Subtype.ext
  show cInvA6Perm * aA6Perm * cInvA6Perm⁻¹ = aA6Perm⁻¹
  decide +kernel

private def cSqA6Perm : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 4 2 * Equiv.swap 2 5

theorem isConj_aA6_mul_bA6_sq : IsConj (aA6 * bA6 ^ 2) (aA6 * bA6) := by
  refine isConj_iff.mpr
    ⟨⟨cSqA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩, ?_⟩
  apply Subtype.ext
  show cSqA6Perm * (aA6Perm * bA6Perm ^ 2) * cSqA6Perm⁻¹ = aA6Perm * bA6Perm
  decide +kernel

theorem isConj_aA6_mul_bA6_inv : IsConj (aA6 * bA6) (aA6 * bA6)⁻¹ := by
  refine isConj_iff.mpr
    ⟨⟨cInvA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩, ?_⟩
  apply Subtype.ext
  show cInvA6Perm * (aA6Perm * bA6Perm) * cInvA6Perm⁻¹ = (aA6Perm * bA6Perm)⁻¹
  decide +kernel

@[expose] def uA6Perm : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def vPtA6Perm : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def wPtA6Perm : Equiv.Perm (Fin 6) := Equiv.swap 1 2 * Equiv.swap 2 3

@[expose] def vTrA6Perm : Equiv.Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 4 5

@[expose] def wTrA6Perm : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 2 * Equiv.swap 2 4) * (Equiv.swap 1 3 * Equiv.swap 3 5)

@[expose] def uA6 : alternatingGroup (Fin 6) :=
  ⟨uA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

@[expose] def vPtA6 : alternatingGroup (Fin 6) :=
  ⟨vPtA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

@[expose] def wPtA6 : alternatingGroup (Fin 6) :=
  ⟨wPtA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

@[expose] def vTrA6 : alternatingGroup (Fin 6) :=
  ⟨vTrA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

@[expose] def wTrA6 : alternatingGroup (Fin 6) :=
  ⟨wTrA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

theorem uA6_sq : uA6 ^ 2 = 1 :=
  Subtype.ext (by
    show uA6Perm ^ 2 = 1
    decide +kernel)

theorem uA6_ne_one : uA6 ≠ 1 := by
  decide +kernel

theorem vPtA6_sq : vPtA6 ^ 2 = 1 :=
  Subtype.ext (by
    show vPtA6Perm ^ 2 = 1
    decide +kernel)

theorem commute_uA6_vPtA6 : Commute uA6 vPtA6 := by
  show uA6 * vPtA6 = vPtA6 * uA6
  exact Subtype.ext (by
    show uA6Perm * vPtA6Perm = vPtA6Perm * uA6Perm
    decide +kernel)

theorem wPtA6_pow_three : wPtA6 ^ 3 = 1 :=
  Subtype.ext (by
    show wPtA6Perm ^ 3 = 1
    decide +kernel)

theorem wPtA6_mul_uA6_mul_inv : wPtA6 * uA6 * wPtA6⁻¹ = vPtA6 :=
  Subtype.ext (by
    show wPtA6Perm * uA6Perm * wPtA6Perm⁻¹ = vPtA6Perm
    decide +kernel)

theorem wPtA6_mul_vPtA6_mul_inv : wPtA6 * vPtA6 * wPtA6⁻¹ = uA6 * vPtA6 :=
  Subtype.ext (by
    show wPtA6Perm * vPtA6Perm * wPtA6Perm⁻¹ = uA6Perm * vPtA6Perm
    decide +kernel)

private def cWptA6Perm : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * Equiv.swap 4 3

theorem isConj_wPtA6_aA6 : IsConj wPtA6 aA6 := by
  refine isConj_iff.mpr
    ⟨⟨cWptA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩, ?_⟩
  apply Subtype.ext
  show cWptA6Perm * wPtA6Perm * cWptA6Perm⁻¹ = aA6Perm
  decide +kernel

theorem vTrA6_sq : vTrA6 ^ 2 = 1 :=
  Subtype.ext (by
    show vTrA6Perm ^ 2 = 1
    decide +kernel)

theorem commute_uA6_vTrA6 : Commute uA6 vTrA6 := by
  show uA6 * vTrA6 = vTrA6 * uA6
  exact Subtype.ext (by
    show uA6Perm * vTrA6Perm = vTrA6Perm * uA6Perm
    decide +kernel)

theorem wTrA6_pow_three : wTrA6 ^ 3 = 1 :=
  Subtype.ext (by
    show wTrA6Perm ^ 3 = 1
    decide +kernel)

theorem wTrA6_mul_uA6_mul_inv : wTrA6 * uA6 * wTrA6⁻¹ = vTrA6 :=
  Subtype.ext (by
    show wTrA6Perm * uA6Perm * wTrA6Perm⁻¹ = vTrA6Perm
    decide +kernel)

theorem wTrA6_mul_vTrA6_mul_inv : wTrA6 * vTrA6 * wTrA6⁻¹ = uA6 * vTrA6 :=
  Subtype.ext (by
    show wTrA6Perm * vTrA6Perm * wTrA6Perm⁻¹ = uA6Perm * vTrA6Perm
    decide +kernel)

private def cWtrA6Perm : Equiv.Perm (Fin 6) := Equiv.swap 0 5 * Equiv.swap 2 3

theorem isConj_wTrA6_mul : IsConj wTrA6 (aA6 * bA6) := by
  refine isConj_iff.mpr
    ⟨⟨cWtrA6Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩, ?_⟩
  apply Subtype.ext
  show cWtrA6Perm * wTrA6Perm * cWtrA6Perm⁻¹ = aA6Perm * bA6Perm
  decide +kernel

@[expose] def fourPtElems : Finset (alternatingGroup (Fin 6)) :=
  {1, uA6, vPtA6,
    ⟨Equiv.swap 0 3 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    aA6,
    ⟨Equiv.swap 0 2 * Equiv.swap 2 1, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    ⟨Equiv.swap 0 3 * Equiv.swap 3 1, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    ⟨Equiv.swap 0 3 * Equiv.swap 3 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    wPtA6,
    ⟨Equiv.swap 1 3 * Equiv.swap 3 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩}

@[expose] def fourTrElems : Finset (alternatingGroup (Fin 6)) :=
  {1, uA6,
    ⟨Equiv.swap 0 1 * Equiv.swap 4 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    vTrA6, wTrA6,
    ⟨(Equiv.swap 0 4 * Equiv.swap 4 2) * (Equiv.swap 1 5 * Equiv.swap 5 3),
      Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    ⟨(Equiv.swap 0 2 * Equiv.swap 2 5) * (Equiv.swap 1 3 * Equiv.swap 3 4),
      Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    ⟨(Equiv.swap 0 5 * Equiv.swap 5 2) * (Equiv.swap 1 4 * Equiv.swap 4 3),
      Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    ⟨(Equiv.swap 0 3 * Equiv.swap 3 4) * (Equiv.swap 1 2 * Equiv.swap 2 5),
      Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    ⟨(Equiv.swap 0 4 * Equiv.swap 4 3) * (Equiv.swap 1 5 * Equiv.swap 5 2),
      Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    ⟨(Equiv.swap 0 3 * Equiv.swap 3 5) * (Equiv.swap 1 2 * Equiv.swap 2 4),
      Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩,
    ⟨(Equiv.swap 0 5 * Equiv.swap 5 3) * (Equiv.swap 1 4 * Equiv.swap 4 2),
      Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩}

@[expose] def fourPtA6 : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {σ | σ ∈ fourPtElems}
  one_mem' := by decide +kernel
  mul_mem' := by
    intro x y hx hy
    change x ∈ fourPtElems at hx
    change y ∈ fourPtElems at hy
    simp only [fourPtElems, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide +kernel
  inv_mem' := by
    intro x hx
    change x ∈ fourPtElems at hx
    simp only [fourPtElems, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide +kernel

@[expose] def fourTrA6 : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {σ | σ ∈ fourTrElems}
  one_mem' := by decide +kernel
  mul_mem' := by
    intro x y hx hy
    change x ∈ fourTrElems at hx
    change y ∈ fourTrElems at hy
    simp only [fourTrElems, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide +kernel
  inv_mem' := by
    intro x hx
    change x ∈ fourTrElems at hx
    simp only [fourTrElems, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide +kernel

private def fourPtEquiv : fourPtA6 ≃ ↥fourPtElems where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def fourTrEquiv : fourTrA6 ≃ ↥fourTrElems where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_fourPtA6 : Nat.card fourPtA6 = 12 := by
  rw [Nat.card_congr fourPtEquiv, Nat.card_congr (Finset.equivFin fourPtElems)]
  simp only [Nat.card_fin]
  decide +kernel

theorem card_fourTrA6 : Nat.card fourTrA6 = 12 := by
  rw [Nat.card_congr fourTrEquiv, Nat.card_congr (Finset.equivFin fourTrElems)]
  simp only [Nat.card_fin]
  decide +kernel

theorem uA6_mem_fourPtA6 : uA6 ∈ fourPtA6 := by
  change uA6 ∈ fourPtElems
  decide +kernel

theorem vPtA6_mem_fourPtA6 : vPtA6 ∈ fourPtA6 := by
  change vPtA6 ∈ fourPtElems
  decide +kernel

theorem wPtA6_mem_fourPtA6 : wPtA6 ∈ fourPtA6 := by
  change wPtA6 ∈ fourPtElems
  decide +kernel

theorem uA6_mem_fourTrA6 : uA6 ∈ fourTrA6 := by
  change uA6 ∈ fourTrElems
  decide +kernel

theorem vTrA6_mem_fourTrA6 : vTrA6 ∈ fourTrA6 := by
  change vTrA6 ∈ fourTrElems
  decide +kernel

theorem wTrA6_mem_fourTrA6 : wTrA6 ∈ fourTrA6 := by
  change wTrA6 ∈ fourTrElems
  decide +kernel

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core
