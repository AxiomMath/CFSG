module

public import Mathlib.GroupTheory.Index

import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutatorElement_mul_right_of_commute {x a b : G} (h : a * ⁅x, b⁆ = ⁅x, b⁆ * a) :
    ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆ := by
  rw [commutatorElement_def] at h
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
  calc x * (a * b) * x⁻¹ * (a * b)⁻¹ = x * a * x⁻¹ * a⁻¹ * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by
        group
    _ = x * a * x⁻¹ * a⁻¹ * ((x * b * x⁻¹ * b⁻¹) * a * a⁻¹) := by rw [h]
    _ = x * a * x⁻¹ * a⁻¹ * (x * b * x⁻¹ * b⁻¹) := by group

@[expose] def commutatorElementHom (x : G) {A Z : Subgroup G} (hZA : Z ≤ centralizer (A : Set G))
    (hxA : ∀ a ∈ A, ⁅x, a⁆ ∈ Z) : A →* Z where
  toFun a := ⟨⁅x, (a : G)⁆, hxA a a.2⟩
  map_one' := Subtype.ext (commutatorElement_one_right x)
  map_mul' a b := Subtype.ext (commutatorElement_mul_right_of_commute
    (mem_centralizer_iff.mp (hZA (hxA b b.2)) a a.2))

theorem commutatorElementHom_apply (x : G) {A Z : Subgroup G} (hZA : Z ≤ centralizer (A : Set G))
    (hxA : ∀ a ∈ A, ⁅x, a⁆ ∈ Z) (a : A) : (commutatorElementHom x hZA hxA a : G) = ⁅x, (a : G)⁆ :=
  rfl

theorem ker_commutatorElementHom (x : G) {A Z : Subgroup G} (hZA : Z ≤ centralizer (A : Set G))
    (hxA : ∀ a ∈ A, ⁅x, a⁆ ∈ Z) :
    (commutatorElementHom x hZA hxA).ker = (A ⊓ centralizer ({x} : Set G)).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · intro ha
    have h1 : ⁅x, (a : G)⁆ = 1 := congrArg Subtype.val ha
    exact ⟨a.2, ((commutatorElement_eq_one_iff_mul_comm).mp h1).symm⟩
  · rintro ⟨-, ha⟩
    exact Subtype.ext ((commutatorElement_eq_one_iff_mul_comm).mpr ha.symm)

variable [Finite G]

theorem relIndex_inf_centralizer_le {D Z A : Subgroup G} (hDZ : ⁅D, D⁆ ≤ Z)
    (hZD : Z ≤ centralizer (D : Set G)) (hAD : A ≤ D) {x : G} (hx : x ∈ D) :
    (A ⊓ centralizer ({x} : Set G)).relIndex A ≤ Nat.card Z := by
  have hZA : Z ≤ centralizer (A : Set G) := hZD.trans (centralizer_le hAD)
  have hxA : ∀ a ∈ A, ⁅x, a⁆ ∈ Z := fun a ha => hDZ (commutator_mem_commutator hx (hAD ha))
  calc (A ⊓ centralizer ({x} : Set G)).relIndex A = (commutatorElementHom x hZA hxA).ker.index := by
        rw [ker_commutatorElementHom]
        rfl
    _ = Nat.card (commutatorElementHom x hZA hxA).range := index_ker _
    _ ≤ Nat.card Z := card_le_card_group _

theorem card_le_card_inf_centralizer_mul_card {D Z A : Subgroup G} (hDZ : ⁅D, D⁆ ≤ Z)
    (hZD : Z ≤ centralizer (D : Set G)) (hAD : A ≤ D) {x : G} (hx : x ∈ D) :
    Nat.card A ≤ Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) * Nat.card Z := by
  have h1 := relIndex_mul_card (A ⊓ centralizer ({x} : Set G)) A
  rw [inf_right_comm, inf_idem] at h1
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul_left _ (relIndex_inf_centralizer_le hDZ hZD hAD hx)

end CFSG.LocalAnalysis.EvenBN.Common
