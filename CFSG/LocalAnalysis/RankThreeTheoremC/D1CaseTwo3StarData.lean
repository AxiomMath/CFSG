module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarData
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3StarPsi

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M R : Subgroup G}

theorem D1CaseTwoData3.caseTwoData_star (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier) (hSyl : KFactCaseTwoSylow)
    (hKO : LocalAnalysis.RankThreeTheoremC.KFactOuterSylowInner) (hC : D1CaseTwoComp3 G)
    {H : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : D1CaseTwoData3 p P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand p M H R z) (hnSP : ¬ D1CzSP p (z : G))
    (hout : D1CzOutside p (z : G)) (hB0 : D1CzB0 p R (z : G)) {Hs : Subgroup G}
    (hHs : GLBIsMaxTwoLocal Hs)
    (hLHs : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ Hs) :
    ∃ Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p),
      D1CaseTwoData3 p P M Hs R Rbars ∧ ∃ hzHs : (z : G) ∈ Hs,
        D1CaseTwoCand p M Hs R ⟨(z : G), hzHs⟩ := by
  obtain ⟨Rbars, hcfg⟩ := D1CaseTwoData3.exists_componentConfig_star hOut hS hC.grp hd hz hHs hLHs
  obtain ⟨hcycs, hzHs, hcand⟩ := hd.toAt.star_core (kFactCycAut_of_kFactOutCyclic hOut) hS
    hInv.toIn hSch hSyl hKO hz hnSP hout hB0 hHs hLHs hcfg.toU hcfg.pRank_rbar_eq_three.le
    (fun _ hK hu hnc hc => hC.false_of_caseThree hcfg (hd.exists_normalCyclic hOut hS hC.grp) hK
      hu hnc hc)
  exact ⟨Rbars, D1CaseTwoData3.of_central hC.central hcfg hcycs, hzHs, hcand⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
