module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenParabolicCommOf
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLin
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSmallU33
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSp
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUni
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlus
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinus
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

open CFSG.Open CFSG.AGLEmbedding

theorem kFactParabolicCommNA_of_group (h : ParabCommGroupOn IsClassicalTwoOrG2) :
    KFactParabolicCommNA := by
  intro A _ _ Y P B p hp hp2 hY h2 hcl hpar hna hB hBY hBP hW
  by_cases hPY : P = Y
  · subst hPY
    exact Or.inl fun c hc y hy =>
      centralizes_of_wCent_self hY h2 (hW c (B.commutator_le_self hc)) y hy
  · exact h A Y P B p hp hp2 hY h2 hcl hpar hPY hna hB hBY hBP hW

theorem parabCommGroupOn_classical (hA : ParabCommGroupOn (IsLieOf IdxA))
    (hU : ParabCommGroupOn (IsLieOf IdxTwistedA)) (hB : ParabCommGroupOn (IsLieOf IdxB))
    (hD : ParabCommGroupOn (IsLieOf IdxD)) (hD' : ParabCommGroupOn (IsLieOf IdxTwistedD))
    (hG : ParabCommGroupOn (IsLieOf IdxG2)) (hS : ParabCommGroupOn IsSmallTwoOrG2) :
    ParabCommGroupOn IsClassicalTwoOrG2 :=
  ParabCommGroupOn.mono
    (parabCommGroupOn_or hA (parabCommGroupOn_or hU (parabCommGroupOn_or hB
      (parabCommGroupOn_or hD (parabCommGroupOn_or hD' (parabCommGroupOn_or hG hS))))))
    fun _ _ h => isClassicalTwoOrG2_family_cases h

theorem kFactParabolicCommNA_of_rest
    (hGA : CFSG.Open.GriessAllModelsStatement) (hU : ParabCommGroupOn (IsLieOf IdxTwistedA))
    (hB : ParabCommGroupOn (IsLieOf IdxB)) (hD : ParabCommGroupOn (IsLieOf IdxD))
    (hD' : ParabCommGroupOn (IsLieOf IdxTwistedD)) (hG : ParabCommGroupOn (IsLieOf IdxG2)) :
    KFactParabolicCommNA :=
  kFactParabolicCommNA_of_group (parabCommGroupOn_classical
    (parabCommOn_idxA_of hGA Lin.linModelComm_holds).group hU hB hD hD' hG parabCommGroupOn_small)

theorem kFactParabolicCommNA_of_orth
    (hGA : CFSG.Open.GriessAllModelsStatement) (hD : ParabCommGroupOn (IsLieOf IdxD))
    (hD' : ParabCommGroupOn (IsLieOf IdxTwistedD)) : KFactParabolicCommNA :=
  kFactParabolicCommNA_of_rest hGA parabCommOn_idxTwistedA_of.group (parabCommOn_idxB_of hGA).group
    hD hD' (GTwo.parabCommOn_idxG2_of hGA).group

theorem kFactParabolicCommNA_of_twistedD
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hD' : ParabCommGroupOn (IsLieOf IdxTwistedD)) : KFactParabolicCommNA :=
  kFactParabolicCommNA_of_orth hGA (parabCommOn_idxD_of hGA).group hD'

theorem kFactParabolicCommNA_holds :
    KFactParabolicCommNA :=
  kFactParabolicCommNA_of_twistedD
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    (parabCommOn_idxTwistedD_of
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement).group

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
