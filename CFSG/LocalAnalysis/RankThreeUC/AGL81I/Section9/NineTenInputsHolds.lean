module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenExceptionalGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenExceptionalRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenMainGen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.LocalAnalysis.RankThreeUC.S15

theorem NineSettingGen.not_outFiveExceptional (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hGA : CFSG.Open.GriessAllModelsStatement) {G : Type} [Group G] [Finite G]
    {M Q H E : Subgroup G} {p : ℕ} (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) (hp3 : 3 < p) {C : Subgroup (StarGroup p H)}
    (hC : CFSG.IsComponent C) :
    ¬ CFSG.LieType.OutStructure.OutFiveExceptional (↥C ⧸ Subgroup.center ↥C) p := by
  intro hex
  obtain ⟨J, hJ, hJC⟩ := exists_isPComponentIn_starImg_eq h.prime hC
  exact h.not_le_of_outFiveExceptional hGA hH2 hp hp3 hC hex hJ hJC
    (h.le_of_outFiveExceptional hS hGA hH2 hp hp3 hC hex hJ hJC)

theorem nineTenInputs_holds :
    NineTenInputs :=
  CFSG.LieType.OutStructure.nineTenInputs_of_exceptional_two (by
    intro G _ _ M Q H E p h hH2 hp hp3 C hC _ hex _
    exact absurd hex (h.not_outFiveExceptional
      CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hH2 hp hp3 hC))

theorem nineTenGen_holds :
    NineTenGen :=
  nineTenGen_of_inputs nineTenInputs_holds

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
