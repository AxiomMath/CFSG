module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSetup

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)
open CFSG.ComponentClassification.RankTwoClassical (Sec3)

@[expose] def E7Sec810 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ExcModel A), D.tag = .E7 →
    Hyp31 A → Odd (Nat.card (center A)) →
      ∃ (R T : Subgroup G) (g : G), Sec3 A R T g ∧ T ⊓ A = ⊥ ∧ rightConjugate R g⁻¹ ⊓ A = ⊥

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
