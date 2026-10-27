module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Round1
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Round2
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.Open.GorensteinWalterLBalanceMilestoneDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G]

theorem k631_core (hSch : CatalogueRelativeB.CatalogueSchreier) (hInn : KFactInnerAction)
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hchar : IsCharTwoType G)
    (hKG : ∀ a : G, a ≠ 1 → IsKGroup ↥(centralizer ({a} : Set G)))
    (hrank : rankThreeLocalRank f G ≤ 3) {E F : Subgroup G} (hEp : IsPGroup f E)
    (hEs : ¬ f ∣ E.index) (hEc : IsMulCommutative E) (hE4 : CFSG.Open.pRank f E = 4)
    (hFE : F ≤ E) (hFe : IsElemAbelian f F) (hF4 : Nat.card F = f ^ 4) {t y g : G}
    (ht : t ^ 2 = 1) (hy1 : y ≠ 1)
    (htF : t ∈ normalizer (F : Set G)) (hgF : g ∈ normalizer (F : Set G))
    (hyF : ∀ a ∈ F, y * a * y⁻¹ = a⁻¹) (hg : g * t * g⁻¹ = t * y) :
    ∃ a ∈ F, a ≠ 1 ∧ ∃ J : Subgroup G, lBalanceIsPComponent f (centralizer ({a} : Set G)) J ∧
      CFSG.Open.pRank f J = 3 ∧ CFSG.Open.pRank f (F ⊓ J) = 3 := by
  have ctx : k631b_Ctx f E F := ⟨hf, hf2, hEp, hEs, hEc, hE4, hFE, hFe, hF4⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hy1
    simpa using hg.symm
  have hU2 := k631b_card_plane hf hf2 hFe hF4 ht htF hgF hyF hg
  obtain ⟨u, huF, hu1, J₁, hJ₁, hlo, hhi, hsum⟩ :=
    k631b_round1 hInn ctx hchar hKG hrank ht ht1 inf_le_left inf_le_right hU2
  have hcase : CFSG.Open.pRank f
        (E ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁) = 1 ∨
      CFSG.Open.pRank f
        (E ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁) = 2 := by
    omega
  rcases hcase with h1 | h2
  · have h3 : CFSG.Open.pRank f (E ⊓ J₁) = 3 := by omega
    exact ⟨u, huF, hu1, J₁, k631b_finish ctx (k631b_layerHyp ctx hKG hrank huF hu1) hJ₁ h3⟩
  · have h3 : CFSG.Open.pRank f (E ⊓ J₁) = 2 := by omega
    obtain ⟨a, haF, ha1, J, hJ, hJ3⟩ :=
      k631b_round2 hSch hInn ctx hchar hKG hrank huF hu1 hJ₁ h2 h3
    exact ⟨a, haF, ha1, J, k631b_finish ctx (k631b_layerHyp ctx hKG hrank haF ha1) hJ hJ3⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
