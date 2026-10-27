module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

section Zpowers

variable {X : Type} [Group X] {z : X}

theorem zpowers_eq_of_orderOf_two (hz : orderOf z = 2) : ∀ x ∈ zpowers z, x = 1 ∨ x = z := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    have : k = 2 * (k / 2) := by omega
    rw [this, zpow_mul]
    simp [hz2]
  · right
    have : k = 2 * (k / 2) + 1 := by omega
    rw [this, zpow_add, zpow_mul]
    simp [hz2]

theorem mem_zpowers_iff_of_orderOf_two (hz : orderOf z = 2) {x : X} :
    x ∈ zpowers z ↔ x = 1 ∨ x = z :=
  ⟨zpowers_eq_of_orderOf_two hz x, by
    rintro (h | h)
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z⟩

theorem normalizer_zpowers_eq_centralizer (hz : orderOf z = 2) :
    normalizer ((zpowers z : Subgroup X) : Set X) = centralizer ({z} : Set X) := by
  ext x
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : x * z * x⁻¹ ∈ zpowers z := (h z).1 (Subgroup.mem_zpowers z)
    rcases zpowers_eq_of_orderOf_two hz _ h1 with h2 | h2
    · exfalso
      have : z = 1 := by
        have := congrArg (fun w => x⁻¹ * w * x) h2
        simpa [mul_assoc] using this
      rw [this, orderOf_one] at hz
      exact absurd hz (by norm_num)
    · have := congrArg (fun w => w * x) h2
      simpa [mul_assoc] using this
  · intro h y
    have hxz : x * z = z * x := h
    constructor
    · intro hy
      rcases zpowers_eq_of_orderOf_two hz y hy with h1 | h1
      · rw [h1]; simp
      · have : x * y * x⁻¹ = y := by rw [h1, hxz]; group
        rw [this]; exact hy
    · intro hy
      rcases zpowers_eq_of_orderOf_two hz _ hy with h2 | h2
      · have : y = 1 := by
          have := congrArg (fun w => x⁻¹ * w * x) h2
          simpa [mul_assoc] using this
        rw [this]
        exact one_mem _
      · have : y = z := by
          have h3 := congrArg (fun w => x⁻¹ * w * x) h2
          have h4 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
          have h5 : x⁻¹ * z * x = z := by rw [mul_assoc, ← hxz]; group
          rw [h4, h5] at h3
          exact h3
        rw [this]
        exact Subgroup.mem_zpowers z

end Zpowers

namespace Sec5Data

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem orderOf_z (h : Sec5Data X n z Z S) : orderOf z = 2 := h.pair.orderOf_z

theorem z_mem (h : Sec5Data X n z Z S) : z ∈ Z := h.pair.mem

theorem isPGroup_Z (h : Sec5Data X n z Z S) : IsPGroup 2 ↥Z := h.pair.sylow.2.1

theorem Z_le_K0 (h : Sec5Data X n z Z S) : Z ≤ K0 X n (normalizer (Z : Set X)) :=
  h.l52.a.1.le.trans (Subgroup.map_subtype_le _)

theorem z_mem_K0 (h : Sec5Data X n z Z S) : z ∈ K0 X n (normalizer (Z : Set X)) :=
  h.Z_le_K0 h.z_mem

theorem K0_ne_bot (h : Sec5Data X n z Z S) : K0 X n (normalizer (Z : Set X)) ≠ ⊥ := by
  intro hbot
  have hz1 : z = 1 := by
    have := h.z_mem_K0
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have := h.orderOf_z
  rw [hz1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem exists_comp (h : Sec5Data X n z Z S) :
    ∃ A : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A ∧ A ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  apply h.K0_ne_bot
  rw [K0_eq_sSup_sec5Comp]
  exact le_bot_iff.1 (sSup_le fun A hA => (hcon A hA).le)

theorem le_normalizer_K0 (X : Type) [Group X] (n : ℕ) (N : Subgroup X) :
    N ≤ normalizer (K0 X n N : Set X) := fun _ hc =>
  mem_normalizer_of_map_conj_eq (map_conj_K0 n (Subgroup.le_normalizer hc))

end Sec5Data

theorem K0_eq_of_sec5Comp_unique {X : Type} [Group X] {n : ℕ} {H : Subgroup X}
    (h1 : ∀ A A' : Subgroup X, Sec5Comp X n H A → Sec5Comp X n H A' → A = A')
    {A : Subgroup X} (hA : Sec5Comp X n H A) : K0 X n H = A := by
  have hset : {B : Subgroup X | Sec5Comp X n H B} = {A} := by
    ext B
    exact ⟨fun hB => h1 B A hB hA, fun hB => by rw [Set.mem_singleton_iff.1 hB]; exact hA⟩
  rw [K0_eq_sSup_sec5Comp, hset, sSup_singleton]

end CFSG.OddStandard.Solomon75
