module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294Assembly
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODLinear
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODUnitaryMono

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

theorem i294OutDiagExcluded_of_inputs (hT : I294ODUnitaryTorus) (hM : I294ODUnitaryMonomial) :
    I294OutDiagExcluded := by
  intro p hp hp5 X _ _ L _ _ hn _ hcen D hD hcard _ _ z g hz hz1 hg hlow hlin
  obtain ⟨x, hxD, hx1, hx2⟩ := hlow
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hlin with ⟨n, K, _, _, hpn, hpK, ⟨e⟩⟩ | ⟨n, q, K, _, _, hKq, hpn, hpq, ⟨e⟩⟩
  · exact od_linear_false hp5 L hn hcen hD hcard hz hz1 hg hxD hx1 hx2 hpn hpK e
  · exact od_unitary_false hT hM hp5 L hn hcen hD hcard hz hz1 hg hxD hx1 hx2 hKq hpn hpq e

theorem i294OutDiagExcluded_holds : I294OutDiagExcluded :=
  i294OutDiagExcluded_of_inputs i294ODUnitaryTorus_holds i294ODUnitaryMonomial_holds

end CFSG.LocalAnalysis.RankFourTheoremC
