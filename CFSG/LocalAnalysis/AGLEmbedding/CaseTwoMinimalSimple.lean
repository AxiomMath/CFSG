module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import Certificates.Certificate113
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
import CFSG.SignalizerFunctorTheorem.CatalogBridge.MinimalSz
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSL2
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.LieType.BorelTits.Suzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.Adapters.Certificate43Check
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Chevalley.EvenRootCommutatorF4
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LieType.Universal.Spin.Roots
import CFSG.LieType.Universal.SpinOmega
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.AGLEmbedding

open CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem isSolvable_of_ne_top_of_isCaseTwoGroup {p : ℕ} {K : Type}
    [Group K] (hK : IsCaseTwoGroup p K) (H : Subgroup K) (hH : H ≠ ⊤) : Group.IsSolvable H := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hK
  rcases hd with ⟨-, q, hqp, hqe, hdq⟩ | ⟨-, hdq⟩
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := CFSG.Adapters.certificate43_holds
    obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 2) (n := 3) (d := ⟨d, hv⟩)
      ⟨q, hdq, hqp, hqe⟩
    exact isSolvable_of_ne_top_of_mulEquiv (e.trans eP)
      (proper_subgroup_solvable_psl2_even Nat.prime_three ⟨1, rfl⟩) H hH
  ·
    simp only at hdq
    subst hdq
    have hiso : CFSG.RankThree.PartOne.Census3.IsoLie K (.suzuki 2) := ⟨hv, ⟨e⟩⟩
    obtain ⟨-, a, -, F, hFf, hFfin, hfa, hF, ⟨eF⟩⟩ :=
      CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
    have ha : a = 2 := by omega
    subst ha
    exact isSolvable_of_ne_top_of_mulEquiv
      ((eF.trans (MulEquiv.subgroupCongr
        (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup 2 F))).trans
        (CFSG.ShultStronglyClosedTI.glaSzEquivNative 2 (by norm_num) hF))
      (isSolvable_of_ne_top_sz (n := 2) (by norm_num)) H hH

end CFSG.AGLEmbedding
