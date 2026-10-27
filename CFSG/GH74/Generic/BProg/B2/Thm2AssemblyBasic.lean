module

public import CFSG.GH74.Generic.BProg.B2.Defs
import CFSG.GH74.Generic.BProg.B2.Thm2Comp
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma113
public import CFSG.GH74.GLS.IVK.L2.Lemma114
public import CFSG.GH74.GLS.IVK.L2.Lemma12ib
public import CFSG.GH74.GLS.IVK.L2.Lemma12j
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.GH74.GLS.IVK.L2.Lemma14f
public import CFSG.GH74.GLS.IVK.L2.Lemma19b
public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.Generic.BProg.B1.Assembly2
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

namespace Thm2AssemblyBasic

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}

theorem isComponent_conjugate {Y : Type*} [Group Y] {J : Subgroup Y} (hJ : IsComponent J) (d : Y) :
    IsComponent (conjugate J d) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj d⁻¹) hJ

theorem components_c1 (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1Core x K M Q H)
    (hc1 : barIn M H = barIn M K) :
    IsComponent (barIn M K) ∧ ∀ J : Subgroup (Mbar M), IsComponent J → J ≠ barIn M K →
      J ≤ SD.centBarK M K := by
  have hHsub : (barIn M H).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) h1.H_min.2.1.2
  have hKc : IsComponent (barIn M K) :=
    isComponent_barIn_of_isSubnormal hs h1.K_le (hc1 ▸ hHsub)
  refine ⟨hKc, fun J hJ hJK => ?_⟩
  rcases CFSG.LocalCores.distinct_components_commute hJ hKc with h | h
  · exact absurd h hJK
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h

omit [Finite G] in
theorem components_c2 (hF : barIn M H = generalizedFitting (Mbar M))
    (hsimp : IsSimpleGroup ↥(barIn M H)) :
    ∀ J : Subgroup (Mbar M), IsComponent J → J = barIn M H := by
  intro J hJ
  have hJF : J ≤ barIn M H := hF ▸ (le_sSup hJ : J ≤ layer (Mbar M)).trans le_sup_right
  have hsub : (J.subgroupOf (barIn M H)).IsSubnormal := hJ.2.subgroupOf
  have hJne : J ≠ ⊥ := fun h => by
    have := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
    rw [h] at this
    exact not_nontrivial_iff_subsingleton.2
      (inferInstance : Subsingleton (⊥ : Subgroup (Mbar M))) this
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hsub with h | h
  · exfalso
    apply hJne
    rw [← Subgroup.map_subgroupOf_eq_of_le hJF, h, Subgroup.map_bot]
  · exact le_antisymm hJF (Subgroup.subgroupOf_eq_top.1 h)

end Thm2AssemblyBasic

end CFSG.GH74.Generic.BProg.B2
