module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Member
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.Open.StatedDefs
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.ClassicalInvolution.Q3.Step
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.Foundations
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.L2.SylowAux
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.IVK.Prod.Basic
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporMult
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCoreBasics
public import CFSG.LocalAnalysis.ComponentClassification.TBLitStepFour
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.J1
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW
public import Certificates.Certificate10025
public import Certificates.Certificate7233Base
public import Certificates.Certificate8171
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

private theorem card_eq_sq_of_card_nine {K : Type} [Field K] (hK : Nat.card K = 9) :
    Nat.card K = (3 ^ 1) ^ 2 := by
  rw [hK]
  norm_num

theorem statedSU_three_quasisimple_center {K : Type} [Field K] [Finite K] (hK : Nat.card K = 9)
    {n : ℕ} (hn : n = 4 ∨ n = 6) :
    IsQuasisimple ↥(StatedSU n 3 K) ∧
      center ↥(StatedSU n 3 K) =
        (StatedScalars (Fin n) K).subgroupOf (StatedSU n 3 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 3) (f := 1)
    (card_eq_sq_of_card_nine hK) (by omega) (by rcases hn with rfl | rfl <;> decide)

theorem card_center_statedSU_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 9)
    {n : ℕ} (hn : n = 4 ∨ n = 6) :
    Nat.card ↥(center ↥(StatedSU n 3 K)) = Nat.gcd n (3 + 1) := by
  rw [(statedSU_three_quasisimple_center hK hn).2]
  exact (CFSG.LinearGroups.unitary_scalar_kernel (p := 3) (f := 1) Nat.prime_three
    (card_eq_sq_of_card_nine hK) (n := n) (by omega)).2.2

theorem lieModel_quotient_statedSU_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 9)
    {n : ℕ} (hn : n = 4 ∨ n = 6) :
    CFSG.Blueprint.LieModel (↥(StatedSU n 3 K) ⧸ center ↥(StatedSU n 3 K)) .PSU n 3 1 := by
  refine Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, by omega, ?_⟩,
    K, inferInstance, inferInstance, card_eq_sq_of_card_nine hK,
    ⟨QuotientGroup.quotientMulEquivOfEq (statedSU_three_quasisimple_center hK hn).2⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  omega

theorem blockData_statedSU
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 9) {n : ℕ} (hn : n = 4 ∨ n = 6) :
    BlockData ↥(StatedSU n 3 K) := by
  have hL := lieModel_quotient_statedSU_three hK hn
  refine ⟨(statedSU_three_quasisimple_center hK hn).1, ?_,
    ⟨.PSU, n, hL, Or.inr (Or.inl ⟨rfl, hn⟩)⟩, ?_⟩
  · rw [card_center_statedSU_three hK hn]
    rcases hn with rfl | rfl
    · exact ⟨2, by norm_num, by norm_num⟩
    · exact ⟨1, le_rfl, by norm_num⟩
  · have hfac := factorization_card_griessHopfMultiplier_psu
      (CFSG.ComponentClassification.TBLit.GriessMultipliersOdd.of_allModels hGA)
      (p := 3) (f := 1) (by norm_num) (by omega)
      (by rcases hn with rfl | rfl <;> decide) hL
    rw [hfac, card_center_statedSU_three hK hn]
    norm_num

end CFSG.OddStandard.HigherRank.F3
