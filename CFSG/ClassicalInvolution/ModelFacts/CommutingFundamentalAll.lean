module

public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalSymplectic
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalUnitary

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank

variable {p : ℕ} [Fact p.Prime]

@[expose] def CommutingFundamentalFactsFive (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), CFSG.ClassicalInvolution.Generic.IsFundTag t →
    StatedLieAdmissible t n p e → 5 ≤ p ^ e → CommutingFundamentalGeneration p t n e

theorem commutingFundamentalFactsFive_of_remaining (hp2 : p ≠ 2)
    (hrest : ∀ (t : StatedLieTag) (n e : ℕ), t ≠ .PSL → t ≠ .PSp → t ≠ .PSU →
      CFSG.ClassicalInvolution.Generic.IsFundTag t → StatedLieAdmissible t n p e → 5 ≤ p ^ e →
        CommutingFundamentalGeneration p t n e) :
    CommutingFundamentalFactsFive p := by
  intro t n e hfund hadm hq
  by_cases hl : t = .PSL
  · subst hl
    exact commutingFundamentalGeneration_psl hp2 hadm
  by_cases hs : t = .PSp
  · subst hs
    exact commutingFundamentalGeneration_psp hp2 hq hadm
  by_cases hu : t = .PSU
  · subst hu
    exact commutingFundamentalGeneration_psu hp2 hadm
  exact hrest t n e hl hs hu hfund hadm hq

end CFSG.ClassicalInvolution.ModelFacts
