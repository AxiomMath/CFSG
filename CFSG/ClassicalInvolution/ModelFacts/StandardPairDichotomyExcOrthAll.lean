module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthE6
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthE7
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthE8
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthF4
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthTw

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank

variable {p : ℕ} [Fact p.Prime]

theorem orthBranch_exceptional {t : StatedLieTag} {e : ℕ}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    (hadm : StatedLieAdmissible t 0 p e) : OrthBranch p t 0 e := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact orthBranch_f4 hadm
  · exact orthBranch_e6 hadm
  · exact orthBranch_e7 hadm
  · exact orthBranch_e8 hadm
  · exact orthBranch_twistedE6 hadm

theorem standardPairDichotomyFE_of_a2Branch
    (hA : ∀ (t : StatedLieTag) (e : ℕ),
      (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
        StatedLieAdmissible t 0 p e → A2Branch p t 0 e) : StandardPairDichotomyFE p :=
  standardPairDichotomyFE_of_branches (fun _ _ ht hadm => orthBranch_exceptional ht hadm) hA

theorem standardPairDichotomyFE_of_a2BranchLeft
    (hA : ∀ (t : StatedLieTag) (e : ℕ),
      (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
        StatedLieAdmissible t 0 p e → A2BranchLeft p t 0 e) : StandardPairDichotomyFE p :=
  standardPairDichotomyFE_of_a2Branch fun t e ht hadm => (hA t e ht hadm).a2Branch

end CFSG.ClassicalInvolution.ModelFacts
