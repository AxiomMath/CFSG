module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrCenter

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

theorem gz9_forall_sylow_of_exists {C : Type} [Group C] [Finite C] (Q : Subgroup C) [Q.Normal]
    {t : C} (ht : ∃ T : Sylow 2 C, t ∈ T ∧ ∃ x ∈ Q,
      (∀ s ∈ (T : Subgroup C) ⊓ commutator C, ⁅x, s⁆ ∈ centerOf Q) ∧ ⁅t, x⁆ ∉ centerOf Q) :
    ∀ T : Sylow 2 C, t ∈ T → ∃ x ∈ Q,
      (∀ s ∈ (T : Subgroup C) ⊓ commutator C, ⁅x, s⁆ ∈ centerOf Q) ∧ ⁅t, x⁆ ∉ centerOf Q := by
  obtain ⟨T₀, htT₀, x₀, hx₀Q, hx₀s, hx₀t⟩ := ht
  intro T htT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C T₀ T
  have hmem : ∀ y : C, y ∈ (T : Subgroup C) ↔ g⁻¹ * y * g ∈ (T₀ : Subgroup C) := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply]
  set t' : C := g⁻¹ * t * g with ht'def
  have ht'T₀ : t' ∈ (T₀ : Subgroup C) := by
    rw [ht'def]; exact (hmem t).mp htT
  set c : C := t⁻¹ * t' with hcdef
  have hc_comm : c = ⁅t⁻¹, g⁻¹⁆ := by
    rw [hcdef, ht'def, commutatorElement_def]; group
  have hcT₀ : c ∈ (T₀ : Subgroup C) := by
    rw [hcdef]
    exact (T₀ : Subgroup C).mul_mem ((T₀ : Subgroup C).inv_mem htT₀) ht'T₀
  have hcC' : c ∈ commutator C := by
    rw [hc_comm, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hx₀c : ⁅x₀, c⁆ ∈ centerOf Q := hx₀s c (Subgroup.mem_inf.mpr ⟨hcT₀, hcC'⟩)
  have htc : t * c = t' := by rw [hcdef, ht'def]; group
  have hcomm_prod : ⁅t', x₀⁆ = t * ⁅c, x₀⁆ * t⁻¹ * ⁅t, x₀⁆ := by
    rw [← htc, commutatorElement_mul_left_eq_conj_mul]
  have hconjc : t * ⁅c, x₀⁆ * t⁻¹ ∈ centerOf Q := by
    have hcx : ⁅c, x₀⁆ = ⁅x₀, c⁆⁻¹ := (commutatorElement_inv (g₁ := x₀) (g₂ := c)).symm
    rw [hcx]
    exact conj_mem_centerOf ((centerOf Q).inv_mem hx₀c) t
  have ht'x₀ : ⁅t', x₀⁆ ∉ centerOf Q := by
    intro hbad
    have htx₀ : ⁅t, x₀⁆ ∈ centerOf Q := by
      have heq : ⁅t, x₀⁆ = (t * ⁅c, x₀⁆ * t⁻¹)⁻¹ * ⁅t', x₀⁆ := by
        rw [hcomm_prod]; group
      rw [heq]
      exact (centerOf Q).mul_mem ((centerOf Q).inv_mem hconjc) hbad
    exact hx₀t htx₀
  refine ⟨g * x₀ * g⁻¹, Subgroup.Normal.conj_mem inferInstance x₀ hx₀Q g, ?_, ?_⟩
  · intro s hs
    obtain ⟨hsT, hsC'⟩ := Subgroup.mem_inf.mp hs
    have hrT₀ : g⁻¹ * s * g ∈ (T₀ : Subgroup C) := (hmem s).mp hsT
    have hrC' : g⁻¹ * s * g ∈ commutator C := by
      simpa using Subgroup.Normal.conj_mem inferInstance s hsC' g⁻¹
    have hr := hx₀s (g⁻¹ * s * g) (Subgroup.mem_inf.mpr ⟨hrT₀, hrC'⟩)
    have hconj : ⁅g * x₀ * g⁻¹, s⁆ = g * ⁅x₀, g⁻¹ * s * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [hconj]
    exact conj_mem_centerOf hr g
  · intro hbad
    have hconj : ⁅t, g * x₀ * g⁻¹⁆ = g * ⁅t', x₀⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; rw [ht'def]; group
    rw [hconj] at hbad
    have heq : g⁻¹ * (g * ⁅t', x₀⁆ * g⁻¹) * (g⁻¹)⁻¹ = ⁅t', x₀⁆ := by group
    exact ht'x₀ (heq ▸ conj_mem_centerOf hbad g⁻¹)

end CFSG.EvenSporadicStandard.HNRecog.Section3
