module

public import CFSG.ClassicalInvolution.Uniform.U5Glue2
public import CFSG.ClassicalInvolution.Uniform.U5Model
public import CFSG.ClassicalInvolution.ModelFacts.CF3TwE6
public import CFSG.ClassicalInvolution.ModelFacts.CF3All

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank



theorem thm5NonGenBelowU_of_modelFacts
    (hTwin : TwinGen3) (hG2D4 : G2D4Gen3) {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) :
    Q3.Disc3.Thm5NonGenBelowU n := by
  refine thm5NonGenBelowU_of_compGen3 (fun t k hfund hadm => ?_) hn
  by_cases h2 : t = .G2 ∨ t = .trialityD4
  · exact hG2D4 t k h2 hfund hadm
  · push Not at h2
    have hComm : ModelFacts.CommutingFundamentalGeneration 3 t k 1 := by
      by_cases hE : t = .twistedE6
      · subst hE
        exact ModelFacts.commutingFundamentalGeneration3_twistedE6 (by norm_num) hadm
      · exact ModelFacts.commutingFundamentalGeneration3_nonTwisted h2.1 h2.2 hE hfund hadm
    exact compGen3_model hfund hadm h2.1 h2.2 hComm (hTwin t k hfund hadm h2.1 h2.2)

end CFSG.ClassicalInvolution.Uniform
