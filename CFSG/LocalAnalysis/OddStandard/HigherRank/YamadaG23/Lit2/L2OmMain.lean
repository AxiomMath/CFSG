module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2PslM
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OmTable
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OmGeneric

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem l2NoPauliPOmega_of_table
    (hG : CFSG.ComponentClassification.HarrisLit.T1.P54.GriessNativeTable) :
    L2NoPauliPOmega := by
  intro S _ _ H _ _ ρ A hρs hq hρk hH2 hE hP hsyl n p f hn5 hno hfam
  obtain ⟨hperf, ζ, hζk, hζ4, hζg⟩ := l2_hopf_cyclic_four hG hno hfam
  rcases hfam with ⟨h4, hX⟩ | ⟨h4, hX⟩
  · obtain ⟨hadm, K, hKf, hKfin, hK, ⟨eS⟩⟩ :=
      hX.statedClassicalModel_of_ne_zero (by omega : n ≠ 0)
    have hpos : 0 < p ^ f := pow_pos hadm.1.pos f
    have hodd : p ^ f % 2 = 1 := by omega
    have h2 : (2 : K) ≠ 0 := by
      refine l2_two_ne_zero ?_
      rw [hK]
      exact hodd
    refine l2_pomega_generic h2 (CFSG.LieType.Universal.Spin.coe_quadPlus n K)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K) ?_ eS hperf hζk hζ4 hζg
      hq ρ hρs hρk hH2 hE hP hsyl
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · obtain ⟨hadm, K, hKf, hKfin, hK, b, c, hirr, ⟨eS⟩⟩ :=
      hX.statedClassicalModel_of_ne_zero (by omega : n ≠ 0)
    have hpos : 0 < p ^ f := pow_pos hadm.1.pos f
    have hodd : p ^ f % 2 = 1 := by omega
    have h2 : (2 : K) ≠ 0 := by
      refine l2_two_ne_zero ?_
      rw [hK]
      exact hodd
    refine l2_pomega_generic h2 (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hirr) ?_ eS
      hperf hζk hζ4 hζg hq ρ hρs hρk hH2 hE hP hsyl
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega

end CFSG.OddStandard.HigherRank.YamadaG23
