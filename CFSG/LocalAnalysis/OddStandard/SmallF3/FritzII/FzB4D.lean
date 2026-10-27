module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBI1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB1A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3J
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB4C

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

theorem fzbs_struct :
    FzbStructProp := by
  intro G _ _ _ t L S x₁ x₂ lam rho tau _ _ h hK
  obtain ⟨f, hF⟩ := fzbs_N2 h
  obtain ⟨T₂, hT⟩ := exists_isFzT2 h.isPGroup (fz_S_le_N2 h)
  obtain ⟨q, hq⟩ := fzbs_exists_gen h
  obtain ⟨P, s, hO⟩ := fzbs_out (fzbs_str_of_ctx h hK hF hT hq)
  exact ⟨T₂, P, q, s,
    { isPGroup := hT.isPGroup
      card_T₂ := fzbs_card_T2 h hK hF hT
      S_le := hT.S_le
      P_le := hO.P_le
      P_norm := hO.P_norm
      card_P := hO.card_P
      P_iso := hO.P_iso
      E_le_P := hO.E_le_P
      rho_norm := hO.rho_norm
      rho_fpf := hO.rho_fpf
      cent_t := hO.cent_t
      q_gen := hq
      s_cases := hO.s_cases
      s_comm_P := hO.s_comm_P
      gen := hO.gen }⟩

end CFSG.OddStandard.SmallF3.FritzII
