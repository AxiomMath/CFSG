module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public meta import Certificates.Data.CFSGNative.SectionRank.F2
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
import CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineSporadicInputs
public import Certificates.Certificate4042
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint

theorem exists_elemAbelian_nine_J2 :
    ∃ E : Subgroup NativeSporadic.J2, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 :=
  Certificates.certificate4042.1

theorem hasElemAb_nine_J2 : HasElemAb 3 9 (NativeSporadic.Carrier .J2) := by
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_nine_J2
  have h9 : Nat.card E = 9 := by rw [hcard]; norm_num
  exact ⟨E, hE, h9⟩

theorem exists_elemAbelian_nine_HS :
    ∃ E : Subgroup NativeSporadic.HS, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 :=
  Certificates.certificate4042.2

theorem hasElemAb_nine_HS : HasElemAb 3 9 (NativeSporadic.Carrier .HS) := by
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_nine_HS
  have h9 : Nat.card E = 9 := by rw [hcard]; norm_num
  exact ⟨E, hE, h9⟩

end CFSG.QuasithinUnique.Id2519
