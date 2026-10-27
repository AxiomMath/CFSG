module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KCr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KFr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18AThm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbInputsHolds
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR10E
import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15G
import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16O
import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE17J
import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18O
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AHolds

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem ctx13K_holds : Ctx13KStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau om hG hc
  have hne := S4B.c13K_exists_not_M hG hc
  unfold Ctx13KFacts
  exact ⟨S4B.c13K_card_K hc hne, S4B.c13K_tK_eq hc hne, S4B.c13K_K_eq hc hne,
    S4B.c13K_CK_rho hc hne⟩

theorem harris1981_bound_reduced13G
    (h411 : Lemma4_11Stmt) (h413 : Lemma4_13Stmt) (hI : Sec4Inputs) :
    FritzII.Harris1981Bound :=
  harris1981_bound_reduced13F (lemma4_1_of_open_steps l41_rabelian_holds l41_q_holds l41_q1_holds
      l41_centq1_holds l41_q1elem_holds l41_final_holds) ctxOfLemma4_1_holds h411 h413 ctx13K_holds hI
    sec4BInputs_holds

end CFSG.OddStandard.SmallF3.HarrisU33
