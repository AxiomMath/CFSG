module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Layer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup CFSG CFSG.LocalCores

variable {K : Type*} [Group K] [Finite K] {z : K} {B : Subgroup K}

omit [Finite K] in
theorem sup_conj (hz : z * z = 1) {L₁ L₂ : Subgroup K}
    (hL₂ : L₂ = L₁.map (MulAut.conj z).toMonoidHom) :
    ∀ x ∈ L₁ ⊔ L₂, z * x * z⁻¹ ∈ L₁ ⊔ L₂ := by
  have hL₁ : L₂.map (MulAut.conj z).toMonoidHom = L₁ := by
    rw [hL₂]; exact map_conj_conj hz L₁
  have hle : L₁ ⊔ L₂ ≤ (L₁ ⊔ L₂).comap (MulAut.conj z).toMonoidHom := by
    refine sup_le ?_ ?_
    · rw [← Subgroup.map_le_iff_le_comap, ← hL₂]
      exact le_sup_right
    · rw [← Subgroup.map_le_iff_le_comap, hL₁]
      exact le_sup_left
  intro x hx
  exact hle hx

omit [Finite K] in
theorem fixed_decomp {N R : Subgroup K} (hNR : N ⊓ R = ⊥) (hN : ∀ x ∈ N, z * x * z⁻¹ ∈ N)
    (hR : ∀ x ∈ R, z * x * z⁻¹ ∈ R) {n r : K} (hn : n ∈ N) (hr : r ∈ R)
    (h : z * (n * r) = (n * r) * z) : z * n = n * z ∧ z * r = r * z := by
  have h1 : (z * n * z⁻¹) * (z * r * z⁻¹) = n * r := by
    calc (z * n * z⁻¹) * (z * r * z⁻¹) = z * (n * r) * z⁻¹ := by group
      _ = n * r := conj_eq_self_iff.2 h
  have h2 : n⁻¹ * (z * n * z⁻¹) = r * (z * r * z⁻¹)⁻¹ := by
    have : n⁻¹ * (z * n * z⁻¹) * (z * r * z⁻¹) = r := by
      calc n⁻¹ * (z * n * z⁻¹) * (z * r * z⁻¹) = n⁻¹ * ((z * n * z⁻¹) * (z * r * z⁻¹)) := by group
        _ = r := by rw [h1]; group
    calc n⁻¹ * (z * n * z⁻¹) = n⁻¹ * (z * n * z⁻¹) * (z * r * z⁻¹) * (z * r * z⁻¹)⁻¹ := by group
      _ = r * (z * r * z⁻¹)⁻¹ := by rw [this]
  have h3 : n⁻¹ * (z * n * z⁻¹) ∈ N ⊓ R := by
    refine ⟨N.mul_mem (N.inv_mem hn) (hN n hn), ?_⟩
    rw [h2]
    exact R.mul_mem hr (R.inv_mem (hR r hr))
  rw [hNR, mem_bot] at h3
  have h4 : z * n * z⁻¹ = n := (inv_mul_eq_one.1 h3).symm
  have h5 : z * r * z⁻¹ = r := by
    rw [h4] at h1
    exact mul_left_cancel h1
  exact ⟨conj_eq_self_iff.1 h4, conj_eq_self_iff.1 h5⟩

theorem center_sup_eq_bot (hF : fittingSubgroup K = ⊥) {L₁ L₂ : Subgroup K}
    (h₁ : IsComponent L₁) (h₂ : IsComponent L₂) :
    ∀ x ∈ L₁ ⊔ L₂, (∀ y ∈ L₁ ⊔ L₂, y * x = x * y) → x = 1 := by
  intro x hx hc
  by_cases hne : L₁ = L₂
  · subst hne
    rw [sup_idem] at hx hc
    exact eq_one_of_commute_of_simple (component_isSimple hF h₁) (component_nonab hF h₁) hx hc
  · have hcom := component_commute h₁ h₂ hne
    have hle : L₂ ≤ centralizer (L₁ : Set K) := fun b hb =>
      mem_centralizer_iff.2 fun a ha => hcom a ha b hb
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hx
    have ha1 : a = 1 := by
      refine eq_one_of_commute_of_simple (component_isSimple hF h₁) (component_nonab hF h₁) ha
        fun y hy => ?_
      have this := hc y (mem_sup_left hy)
      have hyb : y * b = b * y := (hcom y hy b hb)
      have h1 : (y * a) * b = (a * y) * b := by
        calc (y * a) * b = y * (a * b) := by rw [mul_assoc]
          _ = a * b * y := this
          _ = a * (b * y) := by rw [mul_assoc]
          _ = a * (y * b) := by rw [hyb]
          _ = (a * y) * b := by rw [mul_assoc]
      exact mul_right_cancel h1
    have hb1 : b = 1 := by
      refine eq_one_of_commute_of_simple (component_isSimple hF h₂) (component_nonab hF h₂) hb
        fun y hy => ?_
      have this := hc y (mem_sup_right hy)
      have hay : a * y = y * a := hcom a ha y hy
      have h1 : a * (y * b) = a * (b * y) := by
        calc a * (y * b) = (a * y) * b := by rw [mul_assoc]
          _ = (y * a) * b := by rw [hay]
          _ = y * (a * b) := by rw [mul_assoc]
          _ = a * b * y := this
          _ = a * (b * y) := by rw [mul_assoc]
      exact mul_left_cancel h1
    rw [ha1, hb1, one_mul]

end CFSG.EvenSporadicStandard.SolomonRed
