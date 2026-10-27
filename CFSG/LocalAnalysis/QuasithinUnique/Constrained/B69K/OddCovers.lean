module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.OddCoversSurvivor

public section

namespace CFSG.Quasithin.B69K

theorem asSQTKOddCovers_of_table (hGA : CFSG.Open.GriessAllModelsStatement) :
    AsSQTKOddCovers := by
  intro L _ _ hL hodd hgt hS
  exact OddCovers.stronglyQuasithin_of_survivor_cover hGA hL hodd hgt hS

theorem asSQTKOddCovers_holds :
    AsSQTKOddCovers :=
  asSQTKOddCovers_of_table
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end CFSG.Quasithin.B69K

end
