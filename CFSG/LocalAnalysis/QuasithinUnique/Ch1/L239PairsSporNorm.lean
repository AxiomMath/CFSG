module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open scoped commutatorElement

theorem commutator_zpowers_inf_centralizer {G : Type*} [Group G] (U : Subgroup G) (b : G)
    (hb3 : b * b * b = 1) (hnorm : ∀ x ∈ U, b * x * b⁻¹ ∈ U)
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hexp : ∀ x ∈ U, x * x = 1) :
    ⁅U, Subgroup.zpowers b⁆ ≤ U ∧ ∀ u ∈ ⁅U, Subgroup.zpowers b⁆, b * u = u * b → u = 1 := by
  obtain ⟨cj, hcj⟩ : ∃ cj : G → G, ∀ x, cj x = b * x * b⁻¹ := ⟨_, fun _ => rfl⟩
  have hcj_mul : ∀ x y, cj (x * y) = cj x * cj y := by
    intro x y
    rw [hcj, hcj, hcj]
    group
  have hcj_one : cj 1 = 1 := by
    rw [hcj]
    group
  have hcj3 : ∀ x, cj (cj (cj x)) = x := by
    intro x
    rw [hcj, hcj, hcj]
    have : b * (b * (b * x * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * x * (b * b * b)⁻¹ := by group
    rw [this, hb3]
    group
  have hinvU : ∀ x ∈ U, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hexp x hx)
  have hcjU : ∀ x ∈ U, cj x ∈ U := fun x hx => by rw [hcj]; exact hnorm x hx
  obtain ⟨N, hN⟩ : ∃ N : G → G, ∀ x, N x = x * cj x * cj (cj x) := ⟨_, fun _ => rfl⟩
  have hNmul : ∀ x ∈ U, ∀ y ∈ U, N (x * y) = N x * N y := by
    intro x hx y hy
    have hx1 := hcjU x hx
    have hx2 := hcjU _ hx1
    have hy1 := hcjU y hy
    have hy2 := hcjU _ hy1
    rw [hN, hN, hN, hcj_mul, hcj_mul]
    have e1 : y * cj x = cj x * y := hcomm y hy (cj x) hx1
    have e2 : y * cj (cj x) = cj (cj x) * y := hcomm y hy (cj (cj x)) hx2
    have e3 : cj y * cj (cj x) = cj (cj x) * cj y := hcomm _ hy1 _ hx2
    calc x * y * (cj x * cj y) * (cj (cj x) * cj (cj y))
        = x * (y * cj x) * (cj y * cj (cj x)) * cj (cj y) := by group
      _ = x * (cj x * y) * (cj (cj x) * cj y) * cj (cj y) := by rw [e1, e3]
      _ = x * cj x * (y * cj (cj x)) * cj y * cj (cj y) := by group
      _ = x * cj x * (cj (cj x) * y) * cj y * cj (cj y) := by rw [e2]
      _ = (x * cj x * cj (cj x)) * (y * cj y * cj (cj y)) := by group
  have hNcj : ∀ x ∈ U, N (cj x) = N x := by
    intro x hx
    have hx1 := hcjU x hx
    have hx2 := hcjU _ hx1
    rw [hN, hN, hcj3]
    have e : x * (cj x * cj (cj x)) = (cj x * cj (cj x)) * x :=
      hcomm x hx _ (U.mul_mem hx1 hx2)
    calc cj x * cj (cj x) * x = x * (cj x * cj (cj x)) := e.symm
      _ = x * cj x * cj (cj x) := by group
  have hNU : ∀ x ∈ U, N x ∈ U := fun x hx => by
    rw [hN]
    exact U.mul_mem (U.mul_mem hx (hcjU x hx)) (hcjU _ (hcjU x hx))
  have hNsq : ∀ x ∈ U, N x * N x = 1 := fun x hx => hexp _ (hNU x hx)
  have hb3z : b ^ (3 : ℤ) = 1 := by
    have : b ^ (3 : ℕ) = 1 := by simpa [pow_succ] using hb3
    exact_mod_cast this
  have hgen : ∀ x ∈ U, ∀ p ∈ Subgroup.zpowers b, x * p * x⁻¹ * p⁻¹ ∈ U ∧
      N (x * p * x⁻¹ * p⁻¹) = 1 := by
    intro x hx p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
    have hk : b ^ k = b ^ (k % 3) := zpow_eq_zpow_emod k hb3z
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rw [hk, hinvU x hx]
    have hx1 := hcjU x hx
    have hx2 := hcjU _ hx1
    rcases hk3 with h | h | h
    · rw [h, zpow_zero, mul_one, inv_one, mul_one, hexp x hx]
      refine ⟨U.one_mem, ?_⟩
      rw [hN, hcj_one, hcj_one, mul_one, mul_one]
    · rw [h]
      have e : x * b ^ (1 : ℤ) * x * (b ^ (1 : ℤ))⁻¹ = x * cj x := by
        rw [hcj, zpow_one]
        group
      rw [e]
      refine ⟨U.mul_mem hx hx1, ?_⟩
      rw [hNmul x hx _ hx1, hNcj x hx]
      exact hNsq x hx
    · rw [h, zpow_two]
      have e : x * (b * b) * x * (b * b)⁻¹ = x * cj (cj x) := by
        rw [hcj, hcj]
        group
      rw [e]
      refine ⟨U.mul_mem hx hx2, ?_⟩
      rw [hNmul x hx _ hx2, hNcj (cj x) hx1, hNcj x hx]
      exact hNsq x hx
  have hV : ∀ u ∈ ⁅U, Subgroup.zpowers b⁆, u ∈ U ∧ N u = 1 := by
    intro u hu
    rw [Subgroup.commutator_def] at hu
    refine Subgroup.closure_induction (p := fun u _ => u ∈ U ∧ N u = 1) ?_ ?_ ?_ ?_ hu
    · rintro u ⟨x, hx, p, hp, rfl⟩
      exact hgen x hx p hp
    · refine ⟨U.one_mem, ?_⟩
      rw [hN, hcj_one, hcj_one, mul_one, mul_one]
    · rintro u v - - ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
      exact ⟨U.mul_mem hu1 hv1, by rw [hNmul u hu1 v hv1, hu2, hv2, mul_one]⟩
    · rintro u - ⟨hu1, hu2⟩
      rw [hinvU u hu1]
      exact ⟨hu1, hu2⟩
  refine ⟨fun u hu => (hV u hu).1, ?_⟩
  intro u hu hbu
  obtain ⟨hu1, hu2⟩ := hV u hu
  have hcju : cj u = u := by
    rw [hcj, hbu]
    group
  have : N u = u := by
    rw [hN, hcju, hcju]
    have := hexp u hu1
    calc u * u * u = (u * u) * u := rfl
      _ = u := by rw [this, one_mul]
  rw [← this]
  exact hu2

end CFSG.QuasithinUnique.Vol2Native.L239
