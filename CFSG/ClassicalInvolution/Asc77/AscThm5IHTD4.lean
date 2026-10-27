module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHInner
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Model

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance.Q27

@[expose] def TD4OddCoreAll (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .trialityD4 0 p e → p ≠ 2 →
    InvolutionOddCoreTrivial (modelUniv .trialityD4 0 p e Fact.out).K

@[expose] def TD4GenerateAll (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .trialityD4 0 p e → p ≠ 2 →
    InvolutionCentralizersGenerate (modelUniv .trialityD4 0 p e Fact.out).K

variable {p f : ℕ} [Fact p.Prime]

theorem t5BaseAt_td4 (hO : TD4OddCoreAll p) (hG : TD4GenerateAll p) {k e : ℕ} (P : Prop → Prop) :
    T5BaseAt p f .trialityD4 k e P :=
  t5BaseAt_of_model P fun hp2 _ hfund hadm _ => by
    have hk : k = 0 := hadm.2.2
    subst hk
    exact ⟨⟨(ModelFacts.isQuasisimple_modelUniv .trialityD4 0 p e Fact.out hfund hadm).1⟩,
      CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0
        hadm.2.1,
      hO e hadm hp2, hG e hadm hp2⟩

end CFSG.ClassicalInvolution.Asc77
