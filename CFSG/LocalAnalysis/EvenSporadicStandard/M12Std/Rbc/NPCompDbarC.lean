module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPCompA5
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPCompConj

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Equiv Subgroup

variable {K : Type*} [Group K] {A : Subgroup K} [A.Normal]

theorem sign_conjPerm5_eq_one (e : ↥A ≃* alternatingGroup (Fin 5)) {w c : K}
    (hS : Alt5Pair A w c)
    (hab : ∀ a ∈ centralizer ({w} : Set K), ∀ b ∈ centralizer ({w} : Set K), a * b = b * a)
    (hcen : centralizer (A : Set K) ≤ center K) (k : K) : Perm.sign (conjPerm5 e k) = 1 := by
  by_contra h
  have hneg : Perm.sign (conjPerm5 e k) = -1 := by
    rcases Int.units_eq_one_or (Perm.sign (conjPerm5 e k)) with h1 | h1
    · exact absurd h1 h
    · exact h1
  let π₀ : Perm (Fin 5) := (e ⟨c, hS.mem⟩ : Perm (Fin 5))
  have hcΘ : conjPerm5 e c = π₀ := by
    have h0 := conjPerm5_of_mem e ⟨c, hS.mem⟩
    simpa [π₀] using h0
  have hπ₀_sq : π₀ * π₀ = 1 := by
    rw [← hcΘ, ← map_mul, hS.sq_c, map_one]
  have hπ₀_ne : π₀ ≠ 1 := by
    intro h1
    have h2 : e ⟨c, hS.mem⟩ = 1 := by
      apply Subtype.ext
      simpa [π₀] using h1
    have h3 : (⟨c, hS.mem⟩ : ↥A) = 1 := e.injective (by rw [h2, map_one])
    exact hS.ne_one (by simpa using congrArg Subtype.val h3)
  have hEven : ∀ β : Perm (Fin 5), Perm.sign β = 1 →
      ∃ a : ↥A, conjPerm5 e (a : K) = β := by
    intro β hβ
    exact ⟨e.symm ⟨β, Equiv.Perm.mem_alternatingGroup.2 hβ⟩, by
      rw [conjPerm5_of_mem]
      simp⟩
  have hsurj : ∀ α : Perm (Fin 5), ∃ x : K, conjPerm5 e x = α := by
    intro α
    by_cases hα : Perm.sign α = 1
    · obtain ⟨a, ha⟩ := hEven α hα
      exact ⟨(a : K), ha⟩
    · have hαneg : Perm.sign α = -1 := by
        rcases Int.units_eq_one_or (Perm.sign α) with h1 | h1
        · exact absurd h1 hα
        · exact h1
      have hsign : Perm.sign (α * (conjPerm5 e k)⁻¹) = 1 := by
        rw [map_mul, map_inv, hαneg, hneg]
        simp
      obtain ⟨a, ha⟩ := hEven (α * (conjPerm5 e k)⁻¹) hsign
      refine ⟨(a : K) * k, ?_⟩
      rw [map_mul, ha]
      group
  have hlift : ∀ α : Perm (Fin 5), α * π₀ = π₀ * α →
      ∃ x : K, x ∈ centralizer ({w} : Set K) ∧ conjPerm5 e x = α := by
    intro α hα
    obtain ⟨x₀, hx₀⟩ := hsurj α
    have hconjA : x₀ * c * x₀⁻¹ ∈ A := (inferInstance : A.Normal).conj_mem c hS.mem x₀
    have hyΘ : conjPerm5 e (x₀ * c * x₀⁻¹) = π₀ := by
      rw [map_mul, map_mul, map_inv, hx₀, hcΘ, hα]
      group
    have hyc : x₀ * c * x₀⁻¹ = c := by
      have h1 : conjPerm5 e (x₀ * c * x₀⁻¹) = conjPerm5 e c := by rw [hyΘ, hcΘ]
      have h2 : (⟨x₀ * c * x₀⁻¹, hconjA⟩ : ↥A) = ⟨c, hS.mem⟩ := by
        apply e.injective
        apply Subtype.ext
        rw [← conjPerm5_of_mem e ⟨x₀ * c * x₀⁻¹, hconjA⟩,
          ← conjPerm5_of_mem e ⟨c, hS.mem⟩]
        exact h1
      exact congrArg Subtype.val h2
    have hxc : x₀ * c = c * x₀ := mul_inv_eq_iff_eq_mul.mp hyc
    have hh0 : c⁻¹ * w ∈ center K := hcen hS.h₀_mem
    have hx0h0 : x₀ * (c⁻¹ * w) = (c⁻¹ * w) * x₀ :=
      (Subgroup.mem_center_iff.1 hh0) x₀
    have hx0w : x₀ * w = w * x₀ := by
      rw [hS.w_eq]
      calc x₀ * (c * (c⁻¹ * w)) = (x₀ * c) * (c⁻¹ * w) := by group
        _ = (c * x₀) * (c⁻¹ * w) := by rw [hxc]
        _ = c * (x₀ * (c⁻¹ * w)) := by group
        _ = c * ((c⁻¹ * w) * x₀) := by rw [hx0h0]
        _ = c * (c⁻¹ * w) * x₀ := by group
    exact ⟨x₀, Subgroup.mem_centralizer_singleton_iff.2 hx0w, hx₀⟩
  obtain ⟨α, β, hα_comm, hβ_comm, hne⟩ :=
    exists_noncommuting_centralizer_perm5 hπ₀_sq hπ₀_ne
  obtain ⟨x, hx, hxΘ⟩ := hlift α hα_comm
  obtain ⟨y, hy, hyΘ⟩ := hlift β hβ_comm
  exact hne (by rw [← hxΘ, ← hyΘ, ← map_mul, ← map_mul, hab x hx y hy])

end CFSG.EvenSporadicStandard.M12Std.Rbc
