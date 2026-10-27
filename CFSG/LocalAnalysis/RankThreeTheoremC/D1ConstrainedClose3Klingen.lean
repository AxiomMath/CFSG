module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (HasKlingenData)

variable {G : Type} [Group G] [Finite G]

@[expose] def D1CaseThreeKlingen3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) → False

theorem d1CaseThree3_of_klingen (h : D1CaseThreeNotKlingen3 G) (hk : D1CaseThreeKlingen3 G) :
    D1CaseThree3 G := by
  intro p P M H R Rbar hcfg K hK huniq hnc hcent
  have : Fact p.Prime := ⟨hcfg.ext.prime⟩
  by_cases hKD : HasKlingenData p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
  · exact hk p P M H R Rbar hcfg K hK huniq hnc hcent hKD
  · exact h p P M H R Rbar hcfg K hK huniq hnc hcent hKD

theorem d1CaseThreeKlingen3_of_theoremD1 (hD1 : TheoremD1 G) : D1CaseThreeKlingen3 G := by
  intro p _ P M H R Rbar hcfg
  intros
  exact (false_of_extremal_of_theoremD1 hD1 hcfg.glob hcfg.loc.sigma hcfg.loc.isCoreMaxLocal
    hcfg.ext).elim

end CFSG.LocalAnalysis.RankThreeTheoremC
