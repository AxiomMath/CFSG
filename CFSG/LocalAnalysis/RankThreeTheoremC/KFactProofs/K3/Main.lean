module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Transfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Cases
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Reduce

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
  (exists_isComponentOf_of_not_hasPrimeConstraint)

theorem smallRankConstraintKFact3_of_core (hcore : KFactConstraintCore) (hlift : K3LiftThree) :
    SmallRankConstraintKFact3 := by
  intro X _ _ hcat hq hno S hSW hx
  by_contra hnc
  obtain ⟨L, hL⟩ := exists_isComponentOf_of_not_hasPrimeConstraint Nat.prime_three hnc
  obtain ⟨S', hS'W, hx'⟩ := k3_transfer S hSW hx
  have hcatH : CFSG.AGLEmbedding.CatalogSimpleSections (Bar X) :=
    hcat.quotient (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := X) 3)
  have hcoreH : primeComplementCore (G := Bar X) 3 = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.primeComplementCore_bar (G := X)
  rcases components_cases hcoreH S' hS'W hL with
    ⟨L₀, hL₀, huniq⟩ | ⟨L₀, hL₀, hall, hnot⟩
  · obtain ⟨N, hN, hNi⟩ := hcore (Bar X) hcatH hcoreH L₀ hL₀ huniq S' hS'W hx'
    exact k3_no_index_three hno N hN hNi
  · obtain ⟨q, hqp, hq5, hrk⟩ := hlift X hcat S' hS'W L₀ hL₀ hall hnot
    have := hq q hqp hq5
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
