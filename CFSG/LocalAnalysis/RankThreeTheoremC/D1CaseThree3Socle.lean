module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorSocle
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConfigU3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Families

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def StmtChevTwoSocle3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ∀ d : TauCeti.ValidLieTypeIndex, IsChevTwoSurvivorIndex p d →
        Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) →
        Subgroup.center K = ⊥ ∧ IsSimpleGroup K ∧ Nonempty (K ≃* CatGroup d) ∧
          D1SocleConfig K p P M H R (d1LiftX p H R K)

theorem stmtChevTwoSocle3_of (hS : KFactChevTwoSurvivorSchur) : StmtChevTwoSocle3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hcent d hd e
  obtain ⟨e₁⟩ := e
  have hZ : Subgroup.center K = ⊥ :=
    hS K p d hd hK.2.2 (hcfg.isPGroup_center hK) ⟨e₁⟩
  have eK : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  exact ⟨hZ, eK.isSimpleGroup, ⟨eK.trans e₁⟩, hcfg.ext, hcfg.glob.toU.toAGLGlobal,
    d1LiftX_le p H R K, K, normal_of_forall_isComponentOf_eq hK huniq, ⟨MulEquiv.refl _⟩,
    hcfg.centralizer_eq_bot hK huniq hcent hZ, map_d1LiftX p H R K⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
