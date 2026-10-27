module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalTw
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwG2D4
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwE6
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExc

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank

variable {p : ℕ} [Fact p.Prime]

theorem commutingFundamentalGeneration_g2d4Tw (hp2 : p ≠ 2) :
    ∀ (t : StatedLieTag) (n e : ℕ), (t = .G2 ∨ t = .trialityD4 ∨ t = .twistedE6) →
      StatedLieAdmissible t n p e → 5 ≤ p ^ e → CommutingFundamentalGeneration p t n e := by
  rintro t n e (rfl | rfl | rfl) hadm hq
  · exact commutingFundamentalGeneration_g2 hp2 hq hadm
  · exact commutingFundamentalGeneration_trialityD4 hp2 hq hadm
  · exact commutingFundamentalGeneration_twistedE6 hp2 hq hadm

theorem pairFrame_exc_of_tags :
    ∀ (t : StatedLieTag) (e : ℕ) [NeZero e], (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4) →
      p ≠ 2 → 5 ≤ p ^ e → StatedLieAdmissible t 0 p e →
        CFSG.ClassicalInvolution.Balance.Bootstrap.PairFrame (excSignGroup t p e)
          (Generic.fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D) := by
  intro t e _ ht hp2' _ hadm
  exact pairFrame_exc (by rcases ht with h | h | h | h <;> simp [h]) hp2' hadm

theorem commutingFundamentalFactsFive_all (hp2 : p ≠ 2) : CommutingFundamentalFactsFive p := by
  intro t n e hfund hadm hq
  by_cases hs : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedE6
  · exact commutingFundamentalGeneration_g2d4Tw hp2 t n e hs hadm hq
  · simp only [not_or] at hs
    have hnt := CFSG.ClassicalInvolution.Balance.Bootstrap.commutingFundamentalNonTwisted
      (p := p) pairFrame_exc_of_tags
    exact hnt t n e hs.1 hs.2.1 hs.2.2 hfund hadm hp2 hq

end CFSG.ClassicalInvolution.ModelFacts
