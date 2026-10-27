module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def KFactKlingenIdent : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    Open.pRank p (Rb : Subgroup Y) = 3 →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      HasKlingenData p Rb Y₀ → IsKlingenComponent p K

theorem d1CaseThreeKlingenOther3_of_ident (h : KFactKlingenIdent) :
    D1CaseThreeKlingenOther3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD hnot
  exact hnot (h p _ Rbar _ hcfg.red hcfg.catalog hcfg.pRank_rbar_eq_three K hK huniq hnc hcent
    hKD)

end CFSG.LocalAnalysis.RankThreeTheoremC
