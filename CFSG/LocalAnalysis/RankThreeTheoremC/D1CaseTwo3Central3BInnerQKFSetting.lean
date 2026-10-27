module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def KFactCaseTwoFieldInvert : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsCaseTwoGroup 5 K → ∀ φ : MulAut K, φ ^ 5 = 1 →
    (¬ ∃ y : K, φ = MulAut.conj y) → ∀ t : K, orderOf t = 5 → φ t = t →
      ∃ s : K, s ^ 2 = 1 ∧ φ s = s ∧ s * t * s⁻¹ = t⁻¹

end CFSG.LocalAnalysis.RankThreeTheoremC
