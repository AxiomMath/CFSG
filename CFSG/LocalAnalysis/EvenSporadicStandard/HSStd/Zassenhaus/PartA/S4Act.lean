module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup
open scoped commutatorElement

section Act

variable {C : Type*} [Group C]

@[expose] def actKer (O Y : Subgroup C) (hY : Y ≤ center C) : Subgroup C where
  carrier := {g | ∀ o ∈ O, ⁅g, o⁆ ∈ Y}
  mul_mem' := by
    intro g h hg hh o ho
    rw [commutatorElement_mul_left_eq_conj_mul]
    have h1 : g * ⁅h, o⁆ * g⁻¹ = ⁅h, o⁆ := by
      have := Subgroup.mem_center_iff.1 (hY (hh o ho)) g
      rw [this]; group
    rw [h1]
    exact Y.mul_mem (hh o ho) (hg o ho)
  one_mem' := by
    intro o _
    simp
  inv_mem' := by
    intro g hg o ho
    have hy : ⁅o, g⁆ ∈ Y := by
      rw [← commutatorElement_inv]
      exact Y.inv_mem (hg o ho)
    rw [commutatorElement_inv_left]
    have h1 : g⁻¹ * ⁅o, g⁆ * g = ⁅o, g⁆ := by
      rw [Subgroup.mem_center_iff.1 (hY hy) g⁻¹, inv_mul_cancel_right]
    rw [h1]
    exact hy

theorem actKer_conj {O Y : Subgroup C} (hY : Y ≤ center C)
    (hO : ∀ c : C, ∀ o ∈ O, c * o * c⁻¹ ∈ O) {g : C} (hg : g ∈ actKer O Y hY) (c : C) :
    c * g * c⁻¹ ∈ actKer O Y hY := by
  intro o ho
  have h1 : c * ⁅g, c⁻¹ * o * c⁆ * c⁻¹ = ⁅c * g * c⁻¹, o⁆ := by
    rw [commutatorElement_def, commutatorElement_def]; group
  rw [← h1]
  have h2 := hg (c⁻¹ * o * c) (by simpa using hO c⁻¹ o ho)
  have := Subgroup.mem_center_iff.1 (hY h2) c
  rw [this, mul_assoc, mul_inv_cancel, mul_one]
  exact h2

theorem le_actKer {O Y : Subgroup C} (hY : Y ≤ center C)
    (hcomm : ∀ o₁ ∈ O, ∀ o₂ ∈ O, ⁅o₁, o₂⁆ ∈ Y) : O ≤ actKer O Y hY :=
  fun o₁ ho₁ o₂ ho₂ => hcomm o₁ ho₁ o₂ ho₂

theorem commutator_mul_actKer {O Y : Subgroup C} {hY : Y ≤ center C} {g h : C}
    (hh : h ∈ actKer O Y hY) {o : C} (ho : o ∈ O) : ⁅g * h, o⁆ = ⁅h, o⁆ * ⁅g, o⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have := Subgroup.mem_center_iff.1 (hY (hh o ho)) g
  rw [this]; group

theorem commutator_actKer_centralizes {O Y : Subgroup C} (hY : Y ≤ center C) (P : Subgroup C)
    (hP : P ≤ actKer O Y hY) {g h : C} (hg : g ∈ P) (hh : h ∈ P) {o : C} (ho : o ∈ O) :
    ⁅⁅g, h⁆, o⁆ = 1 := by
  let φ : ↥P →* ↥(center C) :=
    { toFun := fun g => ⟨⁅(g : C), o⁆, hY (hP g.2 o ho)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro g h
        apply Subtype.ext
        change ⁅(g : C) * (h : C), o⁆ = ⁅(g : C), o⁆ * ⁅(h : C), o⁆
        rw [commutator_mul_actKer (hP h.2) ho]
        exact (Subgroup.mem_center_iff.1 (hY (hP g.2 o ho)) _) }
  have h1 : φ ⁅(⟨g, hg⟩ : ↥P), ⟨h, hh⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (Subgroup.mem_center_iff.1 (φ ⟨h, hh⟩).2 (φ ⟨g, hg⟩).1))
  have h2 := congrArg Subtype.val h1
  exact h2

end Act

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
