module

public import Mathlib.GroupTheory.Commutator.Basic
import CFSG.GroupTheory.HuppertProduct.CubeIdentity
import CFSG.GroupTheory.HuppertProduct.Quotient
import Mathlib.Tactic.Group

public section

open scoped commutatorElement

namespace CFSG.GroupTheory.HuppertProduct

theorem commutator_pow_three_eq_one {Γ : Type*} [Group Γ] {x g : Γ} (hd : ⁅g, x⁆ ^ 3 = 1)
    (hx : Commute ⁅x, ⁅g, x⁆⁆ x) (hdd : Commute ⁅x, ⁅g, x⁆⁆ ⁅g, x⁆) : ⁅x ^ 3, g⁆ = 1 := by
  set d := ⁅g, x⁆ with hd_def
  set e := ⁅x, d⁆ with he_def
  have h1 : g * x * g⁻¹ = d * x := by
    rw [hd_def, commutatorElement_def]
    group
  have h2 : (d * x) ^ 3 = e ^ 3 * d ^ 3 * x ^ 3 :=
    mul_pow_three_of_commute (x := d) (y := x) hdd hx
  have h3 : e ^ 3 = 1 := by
    rw [he_def, ← commutatorElement_pow_three_of_commute hdd, hd, commutatorElement_one_right]
  have h4 : g * x ^ 3 * g⁻¹ = x ^ 3 := by
    have : g * x ^ 3 * g⁻¹ = (g * x * g⁻¹) ^ 3 := by
      simp [conj_pow]
    rw [this, h1, h2, h3, hd]
    simp
  rw [commutatorElement_def]
  calc x ^ 3 * g * (x ^ 3)⁻¹ * g⁻¹ = x ^ 3 * (g * x ^ 3 * g⁻¹)⁻¹ := by group
    _ = 1 := by rw [h4]; simp

theorem cube_commutator_mem {G : Type*} [Group G] {H K : Subgroup G}
    (hK : H ≤ Subgroup.normalizer (K : Set G)) {x g : G} (hx : x ∈ H) (hg : g ∈ H)
    (hd : ⁅g, x⁆ ^ 3 ∈ K) (hc : ∀ h ∈ H, ⁅⁅x, ⁅g, x⁆⁆, h⁆ ∈ K) : ⁅x ^ 3, g⁆ ∈ K := by
  obtain ⟨Γ, _, π, -, hπ⟩ := exists_quotient hK
  let x' : H := ⟨x, hx⟩
  let g' : H := ⟨g, hg⟩
  have hdH : ⁅g, x⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)) (H.inv_mem hx)
  let d' : H := ⟨⁅g, x⁆, hdH⟩
  have hd' : d' = ⁅g', x'⁆ := rfl
  have hd3 : π d' ^ 3 = 1 := by
    rw [← map_pow]
    exact (hπ _).2 (by simpa [d'] using hd)
  have hcx : ∀ h : H, ⁅π ⁅x', d'⁆, π h⁆ = 1 := by
    intro h
    rw [← map_commutatorElement]
    exact (hπ _).2 (by simpa [x', d', commutatorElement_def] using hc h h.2)
  have key : ⁅π x' ^ 3, π g'⁆ = 1 := by
    refine commutator_pow_three_eq_one (x := π x') (g := π g') ?_ ?_ ?_
    · rw [← map_commutatorElement, ← hd']
      exact hd3
    · rw [← map_commutatorElement, ← map_commutatorElement, ← hd']
      exact commutatorElement_eq_one_iff_commute.1 (hcx x')
    · rw [← map_commutatorElement, ← map_commutatorElement, ← hd']
      exact commutatorElement_eq_one_iff_commute.1 (hcx d')
  have : π ⁅x' ^ 3, g'⁆ = 1 := by
    rw [map_commutatorElement, map_pow]
    exact key
  simpa [x', g', commutatorElement_def] using (hπ _).1 this

end CFSG.GroupTheory.HuppertProduct
