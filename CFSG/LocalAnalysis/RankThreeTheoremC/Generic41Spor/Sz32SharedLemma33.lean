module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Fusion
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0 U3Lemma33)

variable {G : Type} [Group G] [Finite G]

@[expose] def Lemma32Data (p : ℕ) (P : Sylow p G) (x : G) : Prop :=
  (∃ A : Subgroup G, IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧ A ≤ u3S P x ∧
      ∀ s ∈ u3S P x, ∀ a ∈ A, s * a = a * s) ∧
    ∀ E F : Subgroup G, E ≤ u3S P x → IsElemAbelian p E → p ^ 3 ≤ Nat.card E → IsPGroup 2 F →
      F ≤ Subgroup.centralizer ({x} : Set G) → E ≤ Subgroup.normalizer (F : Set G) →
      ∀ a ∈ E, ∀ f ∈ F, a * f = f * a

theorem lemma33_of_lemma32 (hS : Setting G)
    {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
    {J : Subgroup G} (hc : PointConfig Typ G p P M x J) (h : Lemma32Data p P x) : U3Lemma33 p x :=
  CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.lemma33_of_cent hS hc h.1 h.2

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
