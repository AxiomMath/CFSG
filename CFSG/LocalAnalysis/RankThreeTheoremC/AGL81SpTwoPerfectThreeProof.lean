module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroThreePerfectProof
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
import CFSG.LieType.SeitzGeneration.OuterSpData
import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeAltOrder
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLTypeHolds
public import Certificates.Certificate7067
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeChevTwo
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycFive
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycUnique
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFCenter
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFPerfect
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFRest
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoTheoremZ
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroThreeSolv
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NFAxis
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Close
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartOne.CTP.SeitzSpOuter
import CFSG.RankThree.PartOne.CTP.StrongPFinal
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S11d.PSLDescent
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open TauCeti CFSG.Open

theorem three_dvd_ordBC_two {k : ℕ} (hk : 1 ≤ k) : 3 ∣ ordBC k 2 := by
  unfold ordBC
  rw [show Nat.gcd 2 (2 - 1) = 1 by norm_num, Nat.div_one]
  refine Dvd.dvd.mul_left ?_ _
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨le_rfl, hk⟩
  have := Finset.dvd_prod_of_mem (fun i => 2 ^ (2 * i) - 1) h1
  simpa using this

theorem kFactSpTwoPerfectThree_holds : KFactSpTwoPerfectThree := by
  intro X _ _ k d ⟨q, hq, hd⟩ ⟨e⟩ D hD _ hsub
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, he⟩ := CFSG.HardMathSupport.Curtis.Coordinator.PLType.primePower_card_two hq
  have hk2 : 2 ≤ k :=
    ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
  have hk3 : 3 ≤ k := by
    by_contra hk
    obtain rfl : k = 2 := by omega
    have h4 : 4 ≤ q.p ^ q.exponent := by
      have := (TypeB2LieIndex.of q hv).four_le_fieldOrder
      simpa [ValidLieTypeIndex.fieldOrder] using this
    rw [hp, he] at h4
    norm_num at h4
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even k q hv hp hk3 e
  rw [hp, he] at hm
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm
  haveI : IsSimpleGroup (StatedProj (StatedSp k K)) :=
    CFSG.LieType.SeitzGeneration.isSimpleGroup_statedProj_statedSp_of_two_le (by omega)
      (fun h => by omega)
  haveI : IsSimpleGroup X := e'.isSimpleGroup
  rcases CZeroThreePerfect.eq_bot_or_eq_top_of_isSubnormal hsub with h | h
  · exact absurd h hD
  · rw [h, Subgroup.card_top]
    have hcard := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even k q hv hp hk3 e)
    rw [hp, he, pow_one] at hcard
    rw [hcard]
    exact three_dvd_ordBC_two (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC
