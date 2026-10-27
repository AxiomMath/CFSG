module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Diag
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Lev
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7NR

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Data.L_le_nclL_sup (h : d.Hyp) (hKU : d.KUnitary) {K₀ : Subgroup G}
    (hK : d.IsUnitaryFactor K₀)
    (hc : ⁅d.nclL K₀, (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom⁆ = ⊥) :
    d.L ≤ d.nclL K₀ ⊔ (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Data.nclL_delta_surj h hKU hK hc y hy
  have hx' : d.t * x * d.t⁻¹ ∈ (d.nclL K₀).map (MulAut.conj d.t).toMonoidHom := ⟨x, hx, rfl⟩
  exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hx')


theorem unitaryProduct_of_commutation (hcomm : UnitaryCommutation) : UnitaryProduct := by
  intro G _ _ d h hKU
  obtain ⟨K₀, hK⟩ := hKU.exists_isUnitaryFactor
  have hc := hcomm G d h hKU K₀ hK
  have hK₃ : d.K₃ ≤ d.K := by
    rw [← hKU.centralizer_eq]
    exact inf_le_left
  have hWK : d.W ≤ d.K :=
    (inf_le_left : d.W ≤ d.Y).trans (h.Y_le_K hK₃ (Data.Lev_le_zpowers_sup_K₃ d))
  refine ⟨d.nclL K₀, Data.nclL_perfect hK.commutator_eq, ?_, hc, Data.L_le_nclL_sup h hKU hK hc,
    ?_⟩
  · intro hbot
    have hK₀ : K₀ ≤ ⊥ := hbot ▸ d.le_nclL K₀
    apply hK.not_comm
    intro x y
    have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.1 (hK₀ x.2))
    rw [hx1]
    simp
  · rw [← h.Dsub_eq_nclL_sup hK]
    exact h.normalizer_R_le_normalizer_Dsub hWK

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
