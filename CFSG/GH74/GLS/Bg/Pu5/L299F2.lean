module

public import CFSG.GH74.GLS.Bg.Pu5.L299FC1
public import CFSG.GH74.GLS.Bg.Pu5.L299FStatements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec6

theorem l299f2_of (h44 : II4_44) (hquat : II4_4_quat) (hAut : II4_Aut) (h296 : L296)
    (h294a : L294a) : L299F2 := by
  intro G _ _ z t S hC hcard K hK hQ4 hQnc
  rintro ⟨s, hsC, hss⟩
  have htN : t ∈ normalizer (K : Set G) := mem_normalizer_of_ncard_one hcard hK hC.tC
  have hsN : s ∈ normalizer (K : Set G) := mem_normalizer_of_ncard_one hcard hK hsC
  have hQ : IsSL2Or2A7 (Hat K) := h44 G hC.simple z hC.hz K (rr_pcomp hK) hK.2
  have hφ : phi K s hsN * phi K s hsN = phi K t htN := by
    rw [← phi_mul K hsN hsN]
    exact phi_congr K hss _ _
  have hφ2 : phi K t htN * phi K t htN = 1 := phi_mul_self K htN hC.t_mul_self
  have hninn : phi K t htN ∉ innOf (Hat K) := fun h =>
    not_inducesInner_t h44 hquat h296 hC hcard hK hQ4 hQnc ((phi_mem_inn_iff K htN).1 h)
  have hnf : ¬ IsFAutomorphism (Hat K) (phi K t htN) := fun h =>
    (h294a G z t S hC).1 K hK ⟨htN, h⟩
  exact ((hAut (Hat K) hQ).2.2 (phi K t htN) hφ2).2 hninn hnf (phi K s hsN) hφ

end CFSG.GH74.GLS.Bg.Pu5
