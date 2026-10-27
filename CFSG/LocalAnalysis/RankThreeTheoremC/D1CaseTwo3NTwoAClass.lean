module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAClass
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NTwoAAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Class

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.exists_unique_pCore (hOut : KFactOutCyclic) (hC : D1CaseTwoComp3 G)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoData3 p P M H R Rbar) (hY : pCorePreimage p M ⊓ d1LayerX p H R ≠ ⊥) :
    ∃ (H₀ : Subgroup G) (Rbar₀ : Sylow p (H₀ ⧸ primeComplementCore (G := H₀) p)),
      D1CaseTwoData3 p P M H₀ R Rbar₀ ∧ pCorePreimage p M ⊓ d1LayerX p H₀ R ≠ ⊥ ∧
        D1UniqueOver H₀ R (nclIn H₀ (pCorePreimage p M ⊓ d1LayerX p H₀ R)) :=
  exists_unique_pCore_of (Dat := fun H Rb => D1CaseTwoData3 p P M H R Rb) (fun _ _ hd => hd.toAt)
    (fun _ _ hd _ _ hL hLX₀ hLJ _ hH' hJH' hRH' => hd.competitor_of hOut hC hS hInv hSch hL hLX₀ hLJ
      hH' hJH' hRH') (kFactCycAut_of_kFactOutCyclic hOut) hS hKL hSch h84 hD2 hd hY

end Class

end CFSG.LocalAnalysis.RankThreeTheoremC
