module

public import CFSG.Assembly.DichotomyDefs
public import CFSG.ClassicalInvolution.Q3.LieSystem
public import CFSG.ClassicalInvolution.Q3.Q3WLift
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy
open scoped MatrixGroups commutatorElement

@[expose] def FundConjClosed3 (c : CompData) : Prop :=
  ∀ R ∈ c.fund, ∀ g : c.G, R.map (MulAut.conj g).toMonoidHom ∈ c.fund

section Conj

theorem fundConjClosed3_model (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) :
    FundConjClosed3 (CompData.model t n) := by
  rintro R ⟨g₀, γ, hγ, rfl⟩ g
  refine ⟨g * g₀, γ, hγ, ?_⟩
  exact (conjSub_mul g g₀ _).symm

end Conj

end CFSG.ClassicalInvolution.Q3.Q3OF
