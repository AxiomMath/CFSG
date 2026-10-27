module

public import CFSG.LocalAnalysis.RankThreeUC.GN15Climb2
public import CFSG.LocalAnalysis.RankThreeUC.GN15DQNormal
public import CFSG.LocalAnalysis.RankThreeUC.GN15DQAbsorb

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Open

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem gnAbsorbs_gnQPre (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂)
    (hH : GNAbsorbs T T₁ T₂ (gnHPre T)) : GNAbsorbs T T₁ T₂ (gnQPre T) := by
  obtain ⟨-, h1, -, -, h2, h2c, -⟩ := hP
  exact GNAbsorbs.of_le_mul_normalizer_thompsonJ hX.sylow h1 h2 h2c gnHPre_normal
    (gnQPre_normal hX) gnHPre_le_gnQPre (gnQPre_le_sup_normalizer hX) hH

theorem gnAbsorbs_QD (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂)
    (hH : GNAbsorbs T T₁ T₂ (gnHPre T)) : GNAbsorbs T T₁ T₂ (gnQPre T ⊔ gnDPre T) :=
  GNAbsorbs.sup (gnQPre_normal hX) (gnAbsorbs_gnQPre hX hP hH) (gnAbsorbs_gnDPre hX)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
