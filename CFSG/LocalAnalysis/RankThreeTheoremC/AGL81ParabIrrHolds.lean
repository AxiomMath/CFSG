module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenParabolicOf
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrUni
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrSp
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthPlus
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrGTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthMinus
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

theorem kFactParabolicIrredCentralNA_of_on (h : ParabIrrOn IsClassicalTwoOrG2) :
    KFactParabolicIrredCentralNA := by
  intro A _ _ Y P B N p hp hp2 hY h2 hcl hpar hna hB hcyc hBY hBP hW hNY hNP hNB hirr
  by_cases hPY : P = Y
  · subst hPY
    exact Or.inl fun b hb y hy => centralizes_of_wCent_self hY h2 (hW b hb) y hy
  · exact h A Y P B N p hp hp2 hY h2 hcl hpar hPY hna hB hcyc hBY hBP hW hNY hNP hNB hirr

theorem parabIrrOn_classical (hA : ParabIrrOn (IsLieOf IdxA))
    (hU : ParabIrrOn (IsLieOf IdxTwistedA)) (hB : ParabIrrOn (IsLieOf IdxB))
    (hD : ParabIrrOn (IsLieOf IdxD)) (hD' : ParabIrrOn (IsLieOf IdxTwistedD))
    (hG : ParabIrrOn (IsLieOf IdxG2)) (hS : ParabIrrOn IsSmallTwoOrG2) :
    ParabIrrOn IsClassicalTwoOrG2 :=
  ParabIrrOn.mono
    (parabIrrOn_or hA (parabIrrOn_or hU (parabIrrOn_or hB
      (parabIrrOn_or hD (parabIrrOn_or hD' (parabIrrOn_or hG hS))))))
    fun _ _ h => isClassicalTwoOrG2_family_cases h

theorem kFactParabolicIrredCentralNA_of_families (hA : ParabIrrOn (IsLieOf IdxA))
    (hU : ParabIrrOn (IsLieOf IdxTwistedA)) (hB : ParabIrrOn (IsLieOf IdxB))
    (hD : ParabIrrOn (IsLieOf IdxD)) (hD' : ParabIrrOn (IsLieOf IdxTwistedD))
    (hG : ParabIrrOn (IsLieOf IdxG2)) (hS : ParabIrrOn IsSmallTwoOrG2) :
    KFactParabolicIrredCentralNA :=
  kFactParabolicIrredCentralNA_of_on (parabIrrOn_classical hA hU hB hD hD' hG hS)

theorem kFactParabolicIrredCentralNA_of_twistedD
    (hD' : ParabIrrOn (IsLieOf IdxTwistedD)) : KFactParabolicIrredCentralNA := by
  have hGA := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  exact kFactParabolicIrredCentralNA_of_families (parabIrrOn_idxA_of hGA)
    parabIrrOn_idxTwistedA_of (parabIrrOn_idxB_of hGA) (parabIrrOn_idxD_of hGA) hD'
    (parabIrrOn_idxG2_of hGA) (parabIrrOn_small hGA)

theorem kFactParabolicIrredCentralNA_holds :
    KFactParabolicIrredCentralNA :=
  kFactParabolicIrredCentralNA_of_twistedD
    (parabIrrOn_idxTwistedD_of CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr
