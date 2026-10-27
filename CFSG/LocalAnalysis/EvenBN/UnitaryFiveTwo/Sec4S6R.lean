module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6Q

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

section Norm



variable (h : d.Hyp) (hKU : d.KUnitary)

include h hKU in
theorem Data.Hyp.M_le_normalizer_Y :
    d.D₁ ⊓ centralizer ({d.e₂} : Set G) ≤ normalizer (d.Y : Set G) := by
  obtain ⟨K₀, hf⟩ := hKU.exists_isUnitaryFactor
  have hf₁ := Data.IsUnitaryFactor.tc_factor h hf
  intro m hm
  have hmK : m ∈ d.K := h.M_le_K (h.Y_le_K' hKU) (Data.Hyp.K₃_le_K hKU) hm
  have hmK' : m ∈ K₀ ⊔ d.tc K₀ := by rw [← hf.K_eq_tc]; exact hmK
  obtain ⟨a, ha, b, hb, hmab⟩ := KProd.exists_mul_of_mem_sup_of_comm hf.comm_elem hmK'
  have hθa : a * (d.t * a * d.t) ∈ d.X₂ ⊔ d.F := h.theta_component_mem hKU hf hm ha hb hmab
  have hba : b * a = a * b := (hf.comm_elem a ha b hb).symm
  have hθb : b * (d.t * b * d.t) ∈ d.X₂ ⊔ d.F := by
    refine h.theta_component_mem hKU hf₁ hm hb ?_ (by rw [hmab, hba])
    rw [h.tc_tc]
    exact ha
  have hxa : a * (d.t * a * d.t) ∈ normalizer (d.Y : Set G) :=
    h.S_le_normalizer_Y (d.X₂_sup_F_le_S hθa)
  have hxb : b * (d.t * b * d.t) ∈ normalizer (d.Y : Set G) :=
    h.S_le_normalizer_Y (d.X₂_sup_F_le_S hθb)
  refine mem_normalizer_fintype fun y hy => ?_
  have hy' : y ∈ d.Y := hy
  obtain ⟨y₀, hy₀, y₁, hy₁, hyy⟩ := h.exists_mul_of_mem_Y hKU hf hy'
  have e0 : a * y₀ * a⁻¹ ∈ d.Y := by
    have h0 : (a * (d.t * a * d.t)) * y₀ * (a * (d.t * a * d.t))⁻¹ = a * y₀ * a⁻¹ := by
      have := Data.theta_conj_K₀ h hf ⟨a, ha⟩ hy₀.2
      rwa [Data.theta_apply] at this
    rw [← h0]
    exact (mem_normalizer_iff.1 hxa y₀).1 hy₀.1
  have e1 : b * y₁ * b⁻¹ ∈ d.Y := by
    have h0 : (b * (d.t * b * d.t)) * y₁ * (b * (d.t * b * d.t))⁻¹ = b * y₁ * b⁻¹ := by
      have := Data.theta_conj_K₀ h hf₁ ⟨b, hb⟩ hy₁.2
      rwa [Data.theta_apply] at this
    rw [← h0]
    exact (mem_normalizer_iff.1 hxb y₁).1 hy₁.1
  have hby : b * y₀ = y₀ * b := (hf.comm_elem y₀ hy₀.2 b hb).symm
  have hβa : a * (b * y₁ * b⁻¹) = (b * y₁ * b⁻¹) * a :=
    hf.comm_elem a ha _ ((d.tc K₀).mul_mem ((d.tc K₀).mul_mem hb hy₁.2) ((d.tc K₀).inv_mem hb))
  have hcomb : m * y * m⁻¹ = (a * y₀ * a⁻¹) * (b * y₁ * b⁻¹) := by
    rw [hmab, hyy]
    calc a * b * (y₀ * y₁) * (a * b)⁻¹
        = a * (b * y₀) * y₁ * b⁻¹ * a⁻¹ := by group
      _ = a * (y₀ * b) * y₁ * b⁻¹ * a⁻¹ := by rw [hby]
      _ = a * y₀ * ((b * y₁ * b⁻¹) * a⁻¹) := by group
      _ = a * y₀ * (a⁻¹ * (b * y₁ * b⁻¹)) := by rw [comm_inv_of_comm' hβa]
      _ = (a * y₀ * a⁻¹) * (b * y₁ * b⁻¹) := by group
  rw [hcomb]
  exact d.Y.mul_mem e0 e1

end Norm

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
