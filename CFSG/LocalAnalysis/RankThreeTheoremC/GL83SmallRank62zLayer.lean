module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1XLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1XProject
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zMSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {f : ℕ} {X Q : Subgroup G}

theorem k631_comp_inner (hInn : KFactInnerAction) (hL : LayerHyp f X Q) {J : Subgroup G}
    (hJ : GLAPComponent f X J) {q : G} (hq : q ∈ Q) :
    ∃ s ∈ Q ⊓ J, q * s⁻¹ ∈ k631Triv (GLAPPrimeCoreOf f X) J :=
  k631a_comp_inner hInn (k631a_hyp_of_layer hL) hJ hq

theorem k631_comp_triv_inf (hL : LayerHyp f X Q) {J : Subgroup G} (hJ : GLAPComponent f X J) :
    Q ⊓ J ⊓ k631Triv (GLAPPrimeCoreOf f X) J = ⊥ :=
  k631a_triv_inf (k631a_hyp_of_layer hL) hJ

theorem k631_comp_sylow (hL : LayerHyp f X Q) {J : Subgroup G} (hJ : GLAPComponent f X J) :
    ¬ f ∣ ((Q ⊓ J).subgroupOf J).index :=
  k631a_comp_sylow (k631a_hyp_of_layer hL) hJ

theorem k631_decomp (hInn : KFactInnerAction) (hL : LayerHyp f X Q) {J : Subgroup G}
    (hJ : GLAPComponent f X J) :
    Q ≤ (Q ⊓ J) ⊔ (Q ⊓ k631Triv (GLAPPrimeCoreOf f X) J) :=
  k631a_decomp hInn (k631a_hyp_of_layer hL) hJ

theorem k631_layer (hInn : KFactInnerAction) (hL : LayerHyp f X Q) {Y V : Subgroup G}
    (hYX : Y ≤ X) (hY2 : IsPGroup 2 Y) (hVQ : V ≤ Q) (hYV : ⁅Y, V⁆ = Y) : Y ≤ GLAPLayer f X :=
  k631a_layer hInn hL hYX hY2 hVQ hYV

theorem k631_project (hInn : KFactInnerAction) (hL : LayerHyp f X Q) {Y V : Subgroup G}
    (hYX : Y ≤ X) (hY2 : IsPGroup 2 Y) (hY1 : Y ≠ ⊥) (hVQ : V ≤ Q)
    (hVY : V ≤ normalizer (Y : Set G)) (hYV : ⁅Y, V⁆ = Y) :
    ∃ J : Subgroup G, GLAPComponent f X J ∧ ∃ Y₁ : Subgroup G, Y₁ ≠ ⊥ ∧ IsPGroup 2 Y₁ ∧
      (∃ e ∈ Q ⊓ J, e ≠ 1 ∧ e ∈ normalizer (Y₁ : Set G)) ∧
      Q ⊓ k631Triv (GLAPPrimeCoreOf f X) J ≤ normalizer (Y₁ : Set G) :=
  k631a_project hInn hL hYX hY2 hY1 hVQ hVY hYV

theorem k631_involution_centralized (hL : LayerHyp f X Q) {J : Subgroup G}
    (hJ : GLAPComponent f X J) {A : Subgroup G} (hAQ : A ≤ Q)
    (hA : A ≤ k631Triv (GLAPPrimeCoreOf f X) J) :
    ∃ t ∈ J, t ^ 2 = 1 ∧ t ≠ 1 ∧ ∀ a ∈ A, a * t = t * a :=
  k631m_involution_centralized hL hJ hAQ hA

theorem k631_centralizing_sylow (hL : LayerHyp f X Q) {J : Subgroup G}
    (hJ : GLAPComponent f X J) {W A : Subgroup G} (hW : IsPGroup 2 W) (hWL : W ≤ GLAPLayer f X)
    (hAQ : A ≤ Q) (hA : A ≤ k631Triv (GLAPPrimeCoreOf f X) J)
    (hAW : A ≤ normalizer (W : Set G)) (hWA : ⁅W, A⁆ = W) :
    ∃ D : Subgroup G, D ≤ J ⊓ centralizer (W : Set G) ∧ IsPGroup f D ∧
      ¬ f ∣ (D.subgroupOf J).index ∧ ∀ a ∈ A, ∀ d ∈ D, a * d = d * a :=
  k631m_centralizing_sylow hL hJ hW hWL hAQ hA hAW hWA

end CFSG.LocalAnalysis.RankThreeTheoremC
