module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTwin
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSp4Inputs
public import Certificates.Certificate2012
public import Certificates.Certificate77001
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.PushingUpLit.SolK.Inputs
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTable3
public import CFSG.CGT.PushingUpLit.SolKNA.Quaternion
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Assembly
public import CFSG.Foundations
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate43

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QP45 QP45_ok equiv_of_lieModel)

theorem negModel_PSp4 :
    NegModel .PSp 2 := by
  intro X _ _ hX K hK R
  obtain ⟨e⟩ := equiv_of_lieModel hX
  obtain ⟨h1, h2, h3⟩ := Certificates.certificate77001
  refine not_quaternion_of_perm_model QP45 QP45_ok e PSp4Twin.tws h3 (fun t ht => ?_) hK R
  simp only [PSp4Twin.tws, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  exacts [h2, h1]

end CFSG.CGT.PushingUpLit.SolKNA
