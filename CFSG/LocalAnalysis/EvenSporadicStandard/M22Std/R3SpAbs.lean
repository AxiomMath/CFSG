module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3SpExt
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X] {E U : Subgroup X} {z : X}

theorem exists_conj_of_h90 (hz2 : z * z = 1) (hzE : z ∉ E) (hn : ∀ e ∈ E, z * e * z⁻¹ ∈ E)
    (hUE : U ≤ E) (hUS : IsSylowOf 2 U E) (hUz : ∀ u ∈ U, z * u * z⁻¹ ∈ U)
    (hH90 : ∀ u ∈ U, u * (z * u * z⁻¹) = 1 → ∃ v ∈ U, u = v⁻¹ * (z * v * z⁻¹))
    {P : Subgroup X} (hP : IsSylowOf 2 P (extSub E z hz2 hn)) (hzP : z ∈ P)
    {y : X} (hyP : y ∈ P) (hy2 : y * y = 1) (hyE : y ∉ E) : ∃ c ∈ P, y = c⁻¹ * z * c := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hz2' : z⁻¹ * z⁻¹ = 1 := by rw [hzi]; exact hz2
  have hP0S : IsSylowOf 2 (extSub U z hz2 hUz) (extSub E z hz2 hn) :=
    isSylowOf_extSub hUE hzE hUS
  have hzP0 : z ∈ extSub U z hz2 hUz := z_mem_extSub
  have hUP0 : U ≤ extSub U z hz2 hUz := le_extSub
  obtain ⟨k, hkEh, hk⟩ := hP0S.exists_mem_conj hP
  obtain ⟨k, hkE, hk⟩ : ∃ k ∈ E, ∀ x, x ∈ P ↔ k⁻¹ * x * k ∈ extSub U z hz2 hUz := by
    rcases hkEh with h | h
    · exact ⟨k, h, hk⟩
    · refine ⟨k * z, h, fun x => ?_⟩
      rw [hk x]
      have : (k * z)⁻¹ * x * (k * z) = z⁻¹ * (k⁻¹ * x * k) * z := by group
      rw [this]
      constructor
      · intro hx
        exact mul_mem (mul_mem (inv_mem hzP0) hx) hzP0
      · intro hx
        have := mul_mem (mul_mem hzP0 hx) (inv_mem hzP0)
        have e : z * (z⁻¹ * (k⁻¹ * x * k) * z) * z⁻¹ = k⁻¹ * x * k := by group
        rwa [e] at this
  obtain ⟨u0, hu0⟩ : ∃ u0, u0 = k⁻¹ * (z * k * z⁻¹) := ⟨_, rfl⟩
  have hu0E : u0 ∈ E := hu0 ▸ E.mul_mem (E.inv_mem hkE) (hn k hkE)
  have hkzk : k⁻¹ * z * k ∈ extSub U z hz2 hUz := (hk z).1 hzP
  have hu0U : u0 ∈ U := by
    rcases hkzk with h | h
    · exfalso
      apply hzE
      have := E.mul_mem (E.mul_mem hkE (hUE h)) (E.inv_mem hkE)
      simpa [mul_assoc] using this
    · have : u0 = k⁻¹ * z * k * z := by rw [hu0, hzi]; group
      rw [this]
      exact h
  have hcoc : u0 * (z * u0 * z⁻¹) = 1 := by
    calc u0 * (z * u0 * z⁻¹) = k⁻¹ * (z * z) * k * (z⁻¹ * z⁻¹) := by rw [hu0]; group
      _ = 1 := by rw [hz2, hz2']; group
  obtain ⟨v, hvU, hv⟩ := hH90 u0 hu0U hcoc
  obtain ⟨d, hd⟩ : ∃ d, d = k * v⁻¹ := ⟨_, rfl⟩
  have hdE : d ∈ E := hd ▸ E.mul_mem hkE (E.inv_mem (hUE hvU))
  have hzk : z * k * z⁻¹ = k * u0 := by rw [hu0]; group
  have hzv : z * v * z⁻¹ = v * u0 := by rw [hv]; group
  have hdz : z * d * z⁻¹ = d := by
    calc z * d * z⁻¹ = (z * k * z⁻¹) * (z * v * z⁻¹)⁻¹ := by rw [hd]; group
      _ = (k * u0) * (v * u0)⁻¹ := by rw [hzk, hzv]
      _ = k * v⁻¹ := by group
      _ = d := hd.symm
  have hdz' : d * z * d⁻¹ = z := by
    have : z * d = d * z := by
      calc z * d = (z * d * z⁻¹) * z := by group
        _ = d * z := by rw [hdz]
    calc d * z * d⁻¹ = z * d * d⁻¹ := by rw [this]
      _ = z := by group
  have hPd : ∀ x, x ∈ P ↔ d⁻¹ * x * d ∈ extSub U z hz2 hUz := by
    intro x
    rw [hk x]
    have : d⁻¹ * x * d = v * (k⁻¹ * x * k) * v⁻¹ := by rw [hd]; group
    rw [this]
    constructor
    · intro h
      exact mul_mem (mul_mem (hUP0 hvU) h) (inv_mem (hUP0 hvU))
    · intro h
      have := mul_mem (mul_mem (inv_mem (hUP0 hvU)) h) (hUP0 hvU)
      simpa [mul_assoc] using this
  obtain ⟨y', hy'⟩ : ∃ y', y' = d⁻¹ * y * d := ⟨_, rfl⟩
  have hy'P0 : y' ∈ extSub U z hz2 hUz := hy' ▸ (hPd y).1 hyP
  have hy'2 : y' * y' = 1 := by
    calc y' * y' = d⁻¹ * (y * y) * d := by rw [hy']; group
      _ = 1 := by rw [hy2]; group
  have hy'E : y' ∉ E := fun h => hyE (by
    have := E.mul_mem (E.mul_mem hdE h) (E.inv_mem hdE)
    have e : y = d * y' * d⁻¹ := by rw [hy']; group
    rw [e]
    exact this)
  have hu1 : y' * z ∈ U := by
    rcases hy'P0 with h | h
    · exact absurd (hUE h) hy'E
    · exact h
  have hcoc1 : (y' * z) * (z * (y' * z) * z⁻¹) = 1 := by
    calc (y' * z) * (z * (y' * z) * z⁻¹) = y' * (z * z) * y' := by group
      _ = 1 := by rw [hz2, mul_one, hy'2]
  obtain ⟨v1, hv1U, hv1⟩ := hH90 (y' * z) hu1 hcoc1
  have hy'eq : y' = v1⁻¹ * z * v1 := by
    calc y' = (y' * z) * z := by rw [mul_assoc, hz2, mul_one]
      _ = v1⁻¹ * (z * v1 * z⁻¹) * z := by rw [hv1]
      _ = v1⁻¹ * z * v1 := by group
  refine ⟨d * v1 * d⁻¹, (hPd _).2 ?_, ?_⟩
  · have : d⁻¹ * (d * v1 * d⁻¹) * d = v1 := by group
    rw [this]
    exact hUP0 hv1U
  · calc y = d * y' * d⁻¹ := by rw [hy']; group
      _ = d * (v1⁻¹ * z * v1) * d⁻¹ := by rw [hy'eq]
      _ = (d * v1 * d⁻¹)⁻¹ * (d * z * d⁻¹) * (d * v1 * d⁻¹) := by group
      _ = (d * v1 * d⁻¹)⁻¹ * z * (d * v1 * d⁻¹) := by rw [hdz']

end CFSG.EvenSporadicStandard.M22Std
