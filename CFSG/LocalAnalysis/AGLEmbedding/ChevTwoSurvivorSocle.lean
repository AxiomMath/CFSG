module

public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.SocleConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def IsChevTwoSurvivorIndex (p : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q) ∨
    (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .B 2 q) ∨
    (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .G2 q) ∨
    (p = 5 ∧ d.1 = .reeF4 2)

@[expose] def KFactChevTwoSurvivorSchur : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ) (d : TauCeti.ValidLieTypeIndex),
    IsChevTwoSurvivorIndex p d → Open.IsQuasisimple K → IsPGroup p (Subgroup.center K) →
    Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) → Subgroup.center K = ⊥

@[expose] def StmtChevTwoSocle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ∀ d : TauCeti.ValidLieTypeIndex, IsChevTwoSurvivorIndex p d →
        Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) →
        Subgroup.center K = ⊥ ∧ IsSimpleGroup K ∧ Nonempty (K ≃* CatGroup d) ∧
          D1SocleConfig K p P M H R (d1LiftX p H R K)

theorem stmtChevTwoSocle_of (hS : KFactChevTwoSurvivorSchur) : StmtChevTwoSocle := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hcent d hd e
  obtain ⟨e₁⟩ := e
  have hZ : Subgroup.center K = ⊥ :=
    hS K p d hd hK.2.2 (hcfg.isPGroup_center hK) ⟨e₁⟩
  have eK : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  exact ⟨hZ, eK.isSimpleGroup, ⟨eK.trans e₁⟩, hcfg.ext, hcfg.glob, d1LiftX_le p H R K,
    K, normal_of_forall_isComponentOf_eq hK huniq, ⟨MulEquiv.refl _⟩,
    hcfg.centralizer_eq_bot hK huniq hcent hZ, map_d1LiftX p H R K⟩

end CFSG.AGLEmbedding
