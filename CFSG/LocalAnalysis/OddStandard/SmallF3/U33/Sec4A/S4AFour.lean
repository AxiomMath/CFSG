module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem exists_conj_four_mem_PT (h : Ctx t L S x₁ x₂ lam rho tau) {u g₁ : G}
    (hy : u * x₁ ^ 2 = x₁ ^ 2 * u) (hz : u * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * u)
    (hg₁ : g₁ * u * g₁⁻¹ = t) :
    ∃ g : G, g * u * g⁻¹ = t ∧
      (g * x₁ ^ 2 * g⁻¹ ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam ∨
       g * (x₁ * x₂) ^ 2 * g⁻¹ ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam ∨
       g * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * g⁻¹ ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam) := by
  have hy2 : x₁ ^ 2 * x₁ ^ 2 = 1 := (y_mul_self_ne_one h.wreath).1
  have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := (z_mul_self_ne_one h.toCtx0).1
  have hyz : x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 := y_commute_z h.wreath
  let a : G := g₁ * x₁ ^ 2 * g₁⁻¹
  let b : G := g₁ * (x₁ * x₂) ^ 2 * g₁⁻¹
  have ha_def : a = g₁ * x₁ ^ 2 * g₁⁻¹ := rfl
  have hb_def : b = g₁ * (x₁ * x₂) ^ 2 * g₁⁻¹ := rfl
  have ha2 : a * a = 1 := by
    simp only [ha_def]
    calc (g₁ * x₁ ^ 2 * g₁⁻¹) * (g₁ * x₁ ^ 2 * g₁⁻¹)
        = g₁ * (x₁ ^ 2 * x₁ ^ 2) * g₁⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hb2 : b * b = 1 := by
    simp only [hb_def]
    calc (g₁ * (x₁ * x₂) ^ 2 * g₁⁻¹) * (g₁ * (x₁ * x₂) ^ 2 * g₁⁻¹)
        = g₁ * ((x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2) * g₁⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hab : a * b = b * a := by
    simp only [ha_def, hb_def]
    calc (g₁ * x₁ ^ 2 * g₁⁻¹) * (g₁ * (x₁ * x₂) ^ 2 * g₁⁻¹)
        = g₁ * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * g₁⁻¹ := by group
      _ = g₁ * ((x₁ * x₂) ^ 2 * x₁ ^ 2) * g₁⁻¹ := by rw [hyz]
      _ = (g₁ * (x₁ * x₂) ^ 2 * g₁⁻¹) * (g₁ * x₁ ^ 2 * g₁⁻¹) := by group
  have haH : a ∈ invCent t := by
    rw [mem_invCent_iff]
    simp only [ha_def, hg₁.symm]
    calc (g₁ * x₁ ^ 2 * g₁⁻¹) * (g₁ * u * g₁⁻¹)
        = g₁ * (x₁ ^ 2 * u) * g₁⁻¹ := by group
      _ = g₁ * (u * x₁ ^ 2) * g₁⁻¹ := by rw [← hy]
      _ = (g₁ * u * g₁⁻¹) * (g₁ * x₁ ^ 2 * g₁⁻¹) := by group
  have hbH : b ∈ invCent t := by
    rw [mem_invCent_iff]
    simp only [hb_def, hg₁.symm]
    calc (g₁ * (x₁ * x₂) ^ 2 * g₁⁻¹) * (g₁ * u * g₁⁻¹)
        = g₁ * ((x₁ * x₂) ^ 2 * u) * g₁⁻¹ := by group
      _ = g₁ * (u * (x₁ * x₂) ^ 2) * g₁⁻¹ := by rw [← hz]
      _ = (g₁ * u * g₁⁻¹) * (g₁ * (x₁ * x₂) ^ 2 * g₁⁻¹) := by group
  have hQH : closure ({a, b} : Set G) ≤ invCent t := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact haH
    · exact hbH
  have hQp : IsPGroup 2 (closure ({a, b} : Set G)) := isPGroup_closure_pair hab ha2 hb2
  obtain ⟨k, hkH, hk⟩ :=
    exists_conj_le_of_isPGroup (H := invCent t) (S := S) (Q := closure ({a, b} : Set G))
      hQH hQp h.le_invCent h.isPGroup h.relIndex_odd
  have haQ : a ∈ closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hbQ : b ∈ closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have haS : k * a * k⁻¹ ∈ S := hk a haQ
  have hbS : k * b * k⁻¹ ∈ S := hk b hbQ
  have hKS : twoCore t ⊔ wreathGrp x₁ x₂ lam ≤ S := by
    rw [← h.inf_PL]
    exact inf_le_left
  have hor := mem_or_mem_or_mul_mem_of_relIndex_two hKS h.index_PT haS hbS
  refine ⟨k * g₁, ?_, ?_⟩
  · have hkt : k * t = t * k := mem_invCent_iff.mp hkH
    rw [show (k * g₁) * u * (k * g₁)⁻¹ = k * (g₁ * u * g₁⁻¹) * k⁻¹ by group, hg₁, hkt]
    group
  · rcases hor with h1 | h1 | h1
    · left
      have heq : (k * g₁) * x₁ ^ 2 * (k * g₁)⁻¹ = k * a * k⁻¹ := by
        rw [ha_def]; group
      rw [heq]; exact h1
    · right; left
      have heq : (k * g₁) * (x₁ * x₂) ^ 2 * (k * g₁)⁻¹ = k * b * k⁻¹ := by
        rw [hb_def]; group
      rw [heq]; exact h1
    · right; right
      have heq : (k * g₁) * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (k * g₁)⁻¹
          = (k * a * k⁻¹) * (k * b * k⁻¹) := by
        rw [ha_def, hb_def]; group
      rw [heq]; exact h1

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
