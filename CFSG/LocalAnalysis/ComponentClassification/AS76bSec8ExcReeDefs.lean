module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Ree.LargeReeInvolutionCoordinates

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.ReeSec8

open Subgroup CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.RankTwoExceptional.Exc
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def ReeLevi :
    Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime],
    Nat.card K = 2 ^ (2 * m + 1) →
    ∀ (ht : sylowL m K 1 ∈ F4.reeGamma K m),
      ∃ Dl Ql Hl Ll : Subgroup ↥(F4.reeGamma K m),
        LeviData (zx (⟨_, ht⟩ : ↥(F4.reeGamma K m))) Dl Ql Hl Ll ∧ AutFix Ql Ll ∧
          StatedClassicalModel (rankTwoQuot Ll) .PSL 2 2 (2 * m + 1)

end CFSG.ComponentClassification.RankTwoExceptional.ReeSec8
