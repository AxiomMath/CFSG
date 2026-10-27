module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthJ4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Two

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

theorem orthJ4Two : OrthJ4Two := by
  intro G _ _ A D hD _ hZ hq p ℓ hp
  cases D with
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨Z, hcard, -, h2, -⟩ := orthJ4_of_model (quadPlus n K) (StatedQuadPlus n K)
      (coe_quadPlus n K) (nondegenerate_polarBilin_quadPlus n K)
      (exists_totallySingular_quadPlus (by omega) K)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hZ hp
    refine ⟨Z, h2, ?_⟩
    rw [hcard, hK]
    exact le_of_eq hq
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨Z, hcard, -, h2, -⟩ := orthJ4_of_model (quadMinus n K b c) (StatedQuadMinus n K b c)
      (coe_quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
      (exists_totallySingular_quadMinus hn K b c)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hZ hp
    refine ⟨Z, h2, ?_⟩
    rw [hcard, hK]
    exact le_of_eq hq
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
