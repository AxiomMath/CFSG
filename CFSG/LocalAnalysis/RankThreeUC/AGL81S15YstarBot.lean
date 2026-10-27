module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporCrit

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open

variable {X : Type} [Group X] [Finite X]

theorem ystar_eq_bot_of_isSolvable_quotient {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hquot : Group.IsSolvable (X ⧸ gnC T)) : Ystar T T₁ T₂ = ⊥ := by
  haveI := hquot
  rw [Ystar, iSup_eq_bot]
  intro L
  rw [iSup_eq_bot]
  intro hL
  have hq : CFSG.IsQuasisimple ↥L :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.1.2.2
  exact absurd hq (CFSG.Quasithin.E6.Spor.not_isQuasisimple_of_isSolvable (B := ↥L))

theorem Y0_eq_gnC_of_isSolvable_quotient {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hquot : Group.IsSolvable (X ⧸ gnC T)) : Y0 T T₁ T₂ = gnC T := by
  rw [Y0, ystar_eq_bot_of_isSolvable_quotient hX hquot, MonoidHom.comap_bot]
  exact QuotientGroup.ker_mk' (N := gnC T)

end CFSG.LocalAnalysis.RankThreeUC.S15
