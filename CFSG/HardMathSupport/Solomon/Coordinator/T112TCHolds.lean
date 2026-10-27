module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TTables
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCG23
public import CFSG.HardMathSupport.Solomon.Coordinator.SporCoverQuot
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Untw
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem coverT1068_holds :
    CoverT1068 where
  J3 := sporCover_J3_pRank_quot_le
  McL := sporCover_McL_pRank_ge_five
  Suz := sporCover_Suz_pRank_ge_six
  Fi22 := sporCover_Fi22_pRank_ge_six
  Fi24Prime := sporCover_Fi24Prime_pRank_ge_eight

theorem coverT10112_holds :
    CoverT10112 where
  G23 := hatG23_four_le_pRank
  J3 := sporCover_J3_pRank_ge_four
  McL := sporCover_McL_pRank_ge_four
  Suz := sporCover_Suz_pRank_ge_four
  Fi22 := sporCover_Fi22_pRank_ge_four
  Fi24Prime := sporCover_Fi24Prime_pRank_ge_four

theorem coverT10113_of_tw
    (hTw : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6RankLowerTw) : CoverT10113 where
  e6 := fun L _ _ _ hZ r f hm h3 =>
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.e6RankLowerUntw L 0 r f
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hm) h3).1
      (by rw [hZ])
  twistedE6 := fun L _ _ _ hZ r f hm h3 =>
    (hTw L 0 r f (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hm) h3).1
      (by rw [hZ])

theorem tables112Types_of_multipliers
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hTw : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6RankLowerTw) : Tables112Types :=
  tables112Types_of_cover CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hSpM
    ⟨coverT1068_holds, coverT10112_holds, coverT10113_of_tw hTw⟩

end CFSG.HardMathSupport.Solomon.Coordinator
