module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterOrth
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterFamilies
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.MB3.OddOutSymplectic
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne.OutStructure (OutPNice outPNice_PSp_two outPNice_PSp_ge_three_odd)

theorem meetsInner_PSp_even {T : Type} [Group T] [Finite T] {r ℓ f : ℕ} (hr : 2 ≤ r)
    (hℓ : ℓ = 2) (hm : StatedClassicalModel T .PSp r ℓ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : MeetsInner p T := by
  refine meetsInner_of_outPChain hp ?_
  rcases Nat.eq_or_lt_of_le hr with h2 | h3
  · subst h2
    subst hℓ
    exact (outPNice_PSp_two hp hm).toChain
  · exact (outPNice_PSp_ge_three_odd hp hp2 h3 hm).toChain

open TauCeti in
theorem lieOuterRankFamB : LieOuterRankFam .B := by
  intro S _ _ _ _ idx hidx hS p hp hp2 D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e⟩ := hS
  have hr2 : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1).1
  by_cases hq2 : q.p = 2
  · rcases Nat.eq_or_lt_of_le hr2 with h2 | h3
    · subst h2
      exact meetsInner_PSp_even le_rfl hq2
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) hp hp2 D hD hcard
    · exact meetsInner_PSp_even hr2 hq2
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2 h3 e) hp hp2
        D hD hcard
  · rcases Nat.eq_or_lt_of_le hr2 with h2 | h3
    · subst h2
      exact meetsInner_PSp_two hq2 (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
        hp hp2 D hD hcard
    · exact meetsInner_POmegaOdd (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv
        hq2 h3 e) hp hp2 D hD hcard

open TauCeti in
theorem lieOuterRankFamD : LieOuterRankFam .D := by
  intro S _ _ _ _ idx hidx hS p hp hp2 D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e⟩ := hS
  exact meetsInner_POmegaPlus (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)
    hp hp2 D hD hcard

open TauCeti in
theorem lieOuterRankFamTwistedD : LieOuterRankFam .twistedD := by
  intro S _ _ _ _ idx hidx hS p hp hp2 D hD hcard
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e⟩ := hS
  exact meetsInner_POmegaMinus
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e) hp hp2 D hD hcard

end CFSG.HardMathSupport.Timmesfeld.DefChar
