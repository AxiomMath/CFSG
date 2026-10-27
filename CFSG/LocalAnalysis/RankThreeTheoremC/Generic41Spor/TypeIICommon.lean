module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Endgame
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.KFactDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42Generic
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7KFact

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC KFactWeakClosureHeis
  GenericComponentClass u3_endgame)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G} {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
  {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}

structure TypeIIKFacts : Prop where
  inner : KFactInnerAction
  weak : KFactWeakClosure
  heis : KFactWeakClosureHeis
  sig : SignalizerTwoGroupKFact

structure IIPlane (p : ℕ) (P : Sylow p G) (x : G) (J : Subgroup G) (U : Subgroup G) : Prop where
  elem : IsElemAbelian p U
  card : Nat.card U = p ^ 2
  le : U ≤ u3S P x
  mem : x ∈ U
  card_inf : Nat.card ((U ⊓ u3T P x J : Subgroup G)) = p

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
