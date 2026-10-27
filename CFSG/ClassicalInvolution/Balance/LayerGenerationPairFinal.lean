module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairF4
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairG2
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinMinus
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinOdd
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinPlus

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Assembly.LowTwoRank

variable {p : ℕ} [Fact p.Prime]

theorem commutingFundamentalRemaining
    (hpairE : ∀ (t : StatedLieTag) (e : ℕ) [NeZero e],
      (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4) → p ≠ 2 → 5 ≤ p ^ e → StatedLieAdmissible t 0 p e →
        PairFrame (ModelFacts.excSignGroup t p e)
          (Generic.fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D))
    (htw : ∀ n e : ℕ, StatedLieAdmissible .twistedE6 n p e → p ≠ 2 → 5 ≤ p ^ e →
      ModelFacts.CommutingFundamentalGeneration p .twistedE6 n e) :
    ∀ (t : StatedLieTag) (n e : ℕ), t ≠ .G2 → t ≠ .trialityD4 → Generic.IsFundTag t →
      StatedLieAdmissible t n p e → p ≠ 2 → 5 ≤ p ^ e →
        ModelFacts.CommutingFundamentalGeneration p t n e := by
  intro t n e hG2 hD4 hfund hadm hp2 hq
  have hNe : NeZero e := ⟨by rintro rfl; simp at hq⟩
  cases t with
  | PSL => exact ModelFacts.commutingFundamentalGeneration_psl hp2 hadm
  | PSU => exact ModelFacts.commutingFundamentalGeneration_psu hp2 hadm
  | PSp => exact ModelFacts.commutingFundamentalGeneration_psp hp2 hq hadm
  | POmegaOdd => exact commutingFundamentalGeneration_pOmegaOdd hp2 hq hadm
  | POmegaPlus => exact commutingFundamentalGeneration_pOmegaPlus hp2 hq hadm
  | POmegaMinus => exact commutingFundamentalGeneration_pOmegaMinus hp2 hq hadm
  | G2 => exact absurd rfl hG2
  | trialityD4 => exact absurd rfl hD4
  | F4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact commutingFundamentalGeneration_f4 hp2 hadm
      (hpairE .F4 e (Or.inr (Or.inr (Or.inr rfl))) hp2 hq hadm)
  | E6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact commutingFundamentalGeneration_exc hp2 hq (Or.inl rfl) hadm
      (hpairE .E6 e (Or.inl rfl) hp2 hq hadm)
  | E7 =>
    obtain rfl : n = 0 := hadm.2.2
    exact commutingFundamentalGeneration_exc hp2 hq (Or.inr (Or.inl rfl)) hadm
      (hpairE .E7 e (Or.inr (Or.inl rfl)) hp2 hq hadm)
  | E8 =>
    obtain rfl : n = 0 := hadm.2.2
    exact commutingFundamentalGeneration_exc hp2 hq (Or.inr (Or.inr rfl)) hadm
      (hpairE .E8 e (Or.inr (Or.inr (Or.inl rfl))) hp2 hq hadm)
  | twistedE6 => exact htw n e hadm hp2 hq
  | twistedB2 => exact hfund.elim
  | twistedG2 => exact hfund.elim
  | twistedF4 => exact hfund.elim
  | Tits => exact hfund.elim

theorem layerGenerationHybrid_of_pairFrame
    (hpairE : ∀ (t : StatedLieTag) (e : ℕ) [NeZero e],
      (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4) → p ≠ 2 → 5 ≤ p ^ e → StatedLieAdmissible t 0 p e →
        PairFrame (ModelFacts.excSignGroup t p e)
          (Generic.fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D))
    (htw : ∀ n e : ℕ, StatedLieAdmissible .twistedE6 n p e → p ≠ 2 → 5 ≤ p ^ e →
      ModelFacts.CommutingFundamentalGeneration p .twistedE6 n e) :
    LayerGenerationHybrid p :=
  LayerGenerationHybrid.of_commuting_remaining (commutingFundamentalRemaining hpairE htw)

end CFSG.ClassicalInvolution.Balance.Bootstrap
