module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.Commutator.Basic

import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G] {V : Subgroup G} {x : G}

theorem commutatorElement_mul_commutatorElement (hab : ∀ a ∈ V, ∀ b ∈ V, Commute a b)
    (hn : ∀ v ∈ V, x * v * x⁻¹ ∈ V) {a b : G} (ha : a ∈ V) (hb : b ∈ V) :
    ⁅a, x⁆ * ⁅b, x⁆ = ⁅a * b, x⁆ := by
  have hwa : x * a⁻¹ * x⁻¹ ∈ V := hn _ (V.inv_mem ha)
  have hwb : x * b⁻¹ * x⁻¹ ∈ V := hn _ (V.inv_mem hb)
  calc ⁅a, x⁆ * ⁅b, x⁆ = a * ((x * a⁻¹ * x⁻¹) * b) * (x * b⁻¹ * x⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = a * (b * (x * a⁻¹ * x⁻¹)) * (x * b⁻¹ * x⁻¹) := by rw [(hab _ hwa _ hb).eq]
    _ = a * b * ((x * a⁻¹ * x⁻¹) * (x * b⁻¹ * x⁻¹)) := by group
    _ = a * b * ((x * b⁻¹ * x⁻¹) * (x * a⁻¹ * x⁻¹)) := by rw [(hab _ hwa _ hwb).eq]
    _ = ⁅a * b, x⁆ := by simp only [commutatorElement_def]; group

theorem inv_commutatorElement (hab : ∀ a ∈ V, ∀ b ∈ V, Commute a b)
    (hn : ∀ v ∈ V, x * v * x⁻¹ ∈ V) {a : G} (ha : a ∈ V) : ⁅a, x⁆⁻¹ = ⁅a⁻¹, x⁆ := by
  calc ⁅a, x⁆⁻¹ = (x * a * x⁻¹) * a⁻¹ := by simp only [commutatorElement_def]; group
    _ = a⁻¹ * (x * a * x⁻¹) := (hab _ (hn a ha) _ (V.inv_mem ha)).eq
    _ = ⁅a⁻¹, x⁆ := by simp only [commutatorElement_def]; group

theorem exists_eq_commutator_of_mem_commutator_zpowers (hx2 : x * x = 1)
    (hab : ∀ a ∈ V, ∀ b ∈ V, Commute a b) (hn : ∀ v ∈ V, x * v * x⁻¹ ∈ V) {e : G}
    (he : e ∈ ⁅V, Subgroup.zpowers x⁆) : ∃ v ∈ V, e = ⁅v, x⁆ := by
  let H : Subgroup G :=
    { carrier := {e | ∃ v ∈ V, e = ⁅v, x⁆}
      mul_mem' := by
        rintro _ _ ⟨v₁, hv₁, rfl⟩ ⟨v₂, hv₂, rfl⟩
        exact ⟨v₁ * v₂, V.mul_mem hv₁ hv₂, commutatorElement_mul_commutatorElement hab hn hv₁ hv₂⟩
      one_mem' := ⟨1, V.one_mem, by rw [commutatorElement_one_left]⟩
      inv_mem' := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨v⁻¹, V.inv_mem hv, inv_commutatorElement hab hn hv⟩ }
  have hx2z : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx2
  have hle : ⁅V, Subgroup.zpowers x⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro v hv t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · rw [hm, zpow_mul, hx2z, one_zpow, commutatorElement_one_right]
      exact H.one_mem
    · rw [hm, zpow_add, zpow_mul, hx2z, one_zpow, one_mul, zpow_one]
      exact ⟨v, hv, rfl⟩
  exact hle he

end CFSG.GroupTheory

end
