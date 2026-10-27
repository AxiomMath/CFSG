module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.ABGLocalTools

variable {X : Type} [Group X] {E : Subgroup X} {z : X}

@[expose] def extSub (E : Subgroup X) (z : X) (hz2 : z * z = 1)
    (hn : ∀ e ∈ E, z * e * z⁻¹ ∈ E) : Subgroup X where
  carrier := {x | x ∈ E ∨ x * z ∈ E}
  mul_mem' := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (E.mul_mem hx hy)
    · refine Or.inr ?_
      rw [mul_assoc]
      exact E.mul_mem hx hy
    · refine Or.inr ?_
      have h1 := hn y hy
      rw [hzi] at h1
      have : x * y * z = (x * z) * (z * y * z) := by
        calc x * y * z = x * (z * z) * y * z := by rw [hz2, mul_one]
          _ = (x * z) * (z * y * z) := by group
      rw [this]
      exact E.mul_mem hx h1
    · refine Or.inl ?_
      have h1 := hn _ hy
      rw [hzi] at h1
      have : x * y = (x * z) * (z * (y * z) * z) := by
        calc x * y = x * (z * z) * y * (z * z) := by rw [hz2, mul_one, mul_one]
          _ = (x * z) * (z * (y * z) * z) := by group
      rw [this]
      exact E.mul_mem hx h1
  one_mem' := Or.inl E.one_mem
  inv_mem' := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rintro x (hx | hx)
    · exact Or.inl (E.inv_mem hx)
    · refine Or.inr ?_
      have h1 := hn _ (E.inv_mem hx)
      have : x⁻¹ * z = z * (x * z)⁻¹ * z⁻¹ := by
        calc x⁻¹ * z = x⁻¹ * z⁻¹ := by rw [hzi]
          _ = z * (x * z)⁻¹ * z⁻¹ := by group
      rw [this]
      exact h1

variable {hz2 : z * z = 1} {hn : ∀ e ∈ E, z * e * z⁻¹ ∈ E}

theorem le_extSub : E ≤ extSub E z hz2 hn := fun _ hx => Or.inl hx

theorem z_mem_extSub : z ∈ extSub E z hz2 hn :=
  Or.inr (by rw [hz2]; exact E.one_mem)

theorem extSub_mono {E' : Subgroup X} {hn' : ∀ e ∈ E', z * e * z⁻¹ ∈ E'} (h : E' ≤ E) :
    extSub E' z hz2 hn' ≤ extSub E z hz2 hn := by
  rintro x (hx | hx)
  · exact Or.inl (h hx)
  · exact Or.inr (h hx)

theorem card_extSub [Finite X] (hzE : z ∉ E) :
    Nat.card (extSub E z hz2 hn) = 2 * Nat.card E := by
  have hle : E ≤ extSub E z hz2 hn := le_extSub
  have h1 := Subgroup.relIndex_mul_card E (extSub E z hz2 hn)
  rw [inf_of_le_left hle] at h1
  have h2 : E.relIndex (extSub E z hz2 hn) = 2 := by
    refine Subgroup.index_eq_two_iff.2 ⟨⟨z, z_mem_extSub⟩, fun b => ?_⟩
    show Xor (b * ⟨z, z_mem_extSub⟩ ∈ E.subgroupOf (extSub E z hz2 hn))
      (b ∈ E.subgroupOf (extSub E z hz2 hn))
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases b.2 with hb | hb
    · exact Or.inr ⟨hb, fun h => hzE (by simpa using E.mul_mem (E.inv_mem hb) h)⟩
    · refine Or.inl ⟨hb, fun h => hzE ?_⟩
      simpa using E.mul_mem (E.inv_mem h) hb
  rw [h2] at h1
  exact h1.symm

theorem isSylowOf_extSub [Finite X] {U : Subgroup X} (hUE : U ≤ E)
    {hUz : ∀ u ∈ U, z * u * z⁻¹ ∈ U} (hzE : z ∉ E) (hU : IsSylowOf 2 U E) :
    IsSylowOf 2 (extSub U z hz2 hUz) (extSub E z hz2 hn) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hU ⊢
  obtain ⟨_, hUp, hUidx⟩ := hU
  have hzU : z ∉ U := fun h => hzE (hUE h)
  refine ⟨extSub_mono hUE, ?_, ?_⟩
  · obtain ⟨n, hn'⟩ := hUp.exists_card_eq
    exact IsPGroup.of_card (n := n + 1) (by rw [card_extSub hzU, hn', pow_succ]; ring)
  · have h1 := Subgroup.relIndex_mul_card (extSub U z hz2 hUz) (extSub E z hz2 hn)
    rw [inf_of_le_left (extSub_mono hUE)] at h1
    have h2 := Subgroup.relIndex_mul_card U E
    rw [inf_of_le_left hUE] at h2
    rw [card_extSub hzU, card_extSub hzE] at h1
    have hpos : 0 < Nat.card U := Nat.card_pos
    have h4 : (extSub U z hz2 hUz).relIndex (extSub E z hz2 hn) * Nat.card U = Nat.card E := by
      have : 2 * ((extSub U z hz2 hUz).relIndex (extSub E z hz2 hn) * Nat.card U) =
          2 * Nat.card E := by
        rw [← h1]
        ring
      omega
    have h3 : (extSub U z hz2 hUz).relIndex (extSub E z hz2 hn) = U.relIndex E :=
      Nat.eq_of_mul_eq_mul_right hpos (h4.trans h2.symm)
    rw [h3]
    exact hUidx

end CFSG.EvenSporadicStandard.M22Std
