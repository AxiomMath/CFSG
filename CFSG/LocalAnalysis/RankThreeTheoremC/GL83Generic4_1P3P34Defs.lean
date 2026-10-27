module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedPlanes
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

@[expose] def LineWeaklyClosed {G : Type} [Group G] (y : G) (Q : Subgroup G) : Prop :=
  ∀ g : G, (zpowers y).map (MulAut.conj g).toMonoidHom ≤ Q →
    (zpowers y).map (MulAut.conj g).toMonoidHom = zpowers y

@[expose] def LinesNotWeaklyClosed (p : ℕ) {G : Type} [Group G] (u : G) (Q : Subgroup G) : Prop :=
  ∀ y ∈ Q, y ≠ 1 → y ^ p = 1 → zpowers y ≠ zpowers u →
    zpowers y ≠ ⁅Subgroup.closure {z : G | z ∈ Q ∧ z ^ p = 1},
      Subgroup.closure {z : G | z ∈ Q ∧ z ^ p = 1}⁆ →
    ¬ LineWeaklyClosed y Q

end CFSG.LocalAnalysis.RankThreeTheoremC
