module

public import CFSG.ClassicalInvolution.LBalance.Glauberman
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Inv
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Main
public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakCorr
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.Assembly.Reduction
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximal
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutWClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Comm
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.ClassicalGroups
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveApply
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveComponents
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFixedFactorSylowReduction
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainKGroupTwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKProper
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.InvolutionCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.RankOne

public section

namespace CFSG.ComponentClassification.Walter86.Asc75

open CFSG (conjugate)
open CFSG.CGT.PushingUpLit.CGT6
open CFSG.CGT.PushingUpLit.CGT6.Nine7
open CFSG.ComponentClassification.AschbacherKnownGroup (AschbacherKnownGroupFacts)
open Subgroup

theorem glaubermanAt_holds (X : Type) [Group X] [Finite X] : GlaubermanAt X := by
  intro hX _ heven S K hK hfix
  have hcore : CFSG.pPrimeCore 2 X = ⊥ := by
    rw [CFSG.ClassicalInvolution.pPrimeCore_two_eq_oddCore X, CFSG.oddCore, sSup_eq_bot]
    rintro N ⟨hN, hodd⟩
    rcases hN.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) heven
  have hKle : K ≤ CFSG.ClassicalInvolution.sylowFixingAut (S : Subgroup X) :=
    fun α hα => CFSG.ClassicalInvolution.mem_sylowFixingAut.2 (hfix α hα)
  haveI : Group.IsSolvable (CFSG.ClassicalInvolution.sylowFixingAut (S : Subgroup X)) :=
    CFSG.ClassicalInvolution.glaubermanSylowFixingSolvable X hcore S
  have hsolv : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKle)
  by_contra hne
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  exact Group.IsPerfect.not_isSolvable _ hsolv

variable {G : Type} [Group G] [Finite G]

end CFSG.ComponentClassification.Walter86.Asc75
