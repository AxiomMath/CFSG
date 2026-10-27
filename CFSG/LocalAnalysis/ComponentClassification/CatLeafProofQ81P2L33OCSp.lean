module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCTools
public import Certificates.Certificate2007
public import Certificates.Certificate2012
public import Certificates.Certificate2013
public import Certificates.Certificate2014
public import Certificates.Certificate2015
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.Foundations
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33All
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Alt
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33NonB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Odd
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Spor
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Leaf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Conf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCor441
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Fbar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitProperComplete
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate3085Base
public import Certificates.Certificate5007

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup CFSG.Assembly.LowTwoRank

@[expose] def OddSpHigherRow : Prop :=
  TwoNilpFor fun Y _ => ∃ n p f : ℕ, 3 ≤ n ∧ p ≠ 2 ∧ StatedClassicalModel Y .PSp n p f


theorem twoNilpFor_psp_two :
    TwoNilpFor fun Y _ => ∃ p f : ℕ, p ≠ 2 ∧ StatedClassicalModel Y .PSp 2 p f := by
  intro Y _ _ hY _ _ a ha hP
  obtain ⟨p, f, hp2, h⟩ := hY
  have hY' : Blueprint.LieModel Y .PSp 2 p f := Or.inl ⟨by decide, h⟩
  have haa : a * a = 1 := by rw [← sq, ← ha, pow_orderOf_eq_one]
  exact absurd (isPGroup_quotient_iff_hasNormalPComplement.1 hP)
    (GSThmB.cf81NoNilp Y p f h.1.1 hp2 h.1.2.1 (Or.inl hY') a haa)

theorem oddClsRow_psp_of (h3 : OddSpHigherRow) : OddClsRow .PSp := by
  intro Y _ _ hY
  obtain ⟨n, p, f, hp2, h⟩ := hY
  by_cases hn : 3 ≤ n
  · exact h3 Y ⟨n, p, f, hn, hp2, h⟩
  · have hn2 : n = 2 := by
      obtain ⟨⟨-, -, hn2, -⟩, -⟩ := h
      omega
    subst hn2
    exact twoNilpFor_psp_two Y ⟨p, f, hp2, h⟩

end CFSG.ComponentClassification.HarrisLit.L33.OC
