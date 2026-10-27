module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6R
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6Fin
public import CFSG.Yardstones.M41b0c98b3153.Definitions

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem u52LinearSmallCentralizerExclusion_holds
    : CFSG.Yardstones.M41b0c98b3153.U52LinearSmallCentralizerExclusion := by
  intro G _ _ d h hKl hH
  have hK := h.comm_M_V₂_mem_W_linear hKl
  have hKY := h.M_le_normalizer_Y_linear hKl
  have hD := h.D₁_le_normalizer_D₂ hK hKY
  obtain ⟨B, hBc, hBs, hBcard, hBN⟩ := h.exists_B_lin hKl hD
  exact h.false_of_sylow (Q := d.P) (h.exists_sylow_T hKl hH) (h.t_not_mem_P hK hKY)
    (fun x hx => by rw [h.t_inv]; exact h.t_conj_mem_P hx)
    (h.no_conj_t_mem hBc hBs hBcard hBN)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
