module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

open scoped Pointwise

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem pow_eq_one_of_mem_zpowers_sup {a b : G} {r : ℕ} (hcomm : Commute a b)
    (ha : orderOf a ∣ r) (hb : orderOf b ∣ r)
    {e : G} (he : e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) : e ^ r = 1 := by
  classical
  have hpt : ∀ h ∈ Subgroup.zpowers a, ∀ k ∈ Subgroup.zpowers b, h * k = k * h := by
    intro h hh k hk
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact hcomm.zpow_zpow i j
  have hnorm : Subgroup.zpowers a ≤
      Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : h * y * h⁻¹ = y := by rw [hpt h hh y hy]; group
      change h * y * h⁻¹ ∈ Subgroup.zpowers b
      rwa [h1]
    · intro hx
      refine ⟨x, hx, ?_⟩
      have h1 : h * x * h⁻¹ = x := by rw [hpt h hh x hx]; group
      change h * x * h⁻¹ = x
      rw [h1]
  have he' : e ∈ ((Subgroup.zpowers a : Set G) * (Subgroup.zpowers b : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm]
    exact he
  obtain ⟨h, hh, k, hk, rfl⟩ := Set.mem_mul.mp he'
  have hhr : h ^ r = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hh).trans ha)
  have hkr : k ^ r = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hk).trans hb)
  have hchk : Commute h k := hpt h hh k hk
  simp [hchk.mul_pow, hhr, hkr]

end CFSG.GroupTheory

end
