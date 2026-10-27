module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Member
public import CFSG.Open.StatedDefs
public import CFSG.LieType.Universal.Symplectic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
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

theorem odd_exceptionalOrders_psp {m p f : ℕ} (hp2 : p ≠ 2) :
    Odd ((Blueprint.Multiplier.exceptionalOrders .PSp m p f).1 *
      (Blueprint.Multiplier.exceptionalOrders .PSp m p f).2) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> first | decide | simp_all

theorem factorization_card_griessHopfMultiplier_psp
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {Y : Type} [Group Y] {m p f : ℕ} (hp2 : p ≠ 2) (hm : m ≠ 0)
    (hL : Blueprint.LieModel Y .PSp m p f) :
    (Nat.card (Open.griessHopfMultiplier Y)).factorization 2 =
      (Nat.gcd 2 (p ^ f - 1)).factorization 2 := by
  rw [card_griessHopfMultiplier_eq hGA (models_lieModel_of_lieModel_of_ne_zero hm hL)]
  rw [show Blueprint.Multiplier.genericOrders .PSp m p f = (Nat.gcd 2 (p ^ f - 1), 1) from rfl,
    mul_one]
  exact factorization_two_mul_odd (Nat.gcd_pos_of_pos_left _ two_pos).ne'
    (odd_exceptionalOrders_psp hp2)

theorem card_center_statedSp_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {m : ℕ} (hm : 1 ≤ m) : Nat.card ↥(center ↥(StatedSp m K)) = 2 := by
  have h := LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd K hm
  rw [hK] at h
  rw [LieType.Universal.Symplectic.center_eq m K]
  exact h.trans (by norm_num)

theorem lieModel_quotient_statedSp {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {m : ℕ} (hm : 2 ≤ m) :
    CFSG.Blueprint.LieModel (↥(StatedSp m K) ⧸ center ↥(StatedSp m K)) .PSp m 3 1 := by
  refine Or.inl ⟨by decide, LieType.Universal.Symplectic.statedClassicalModel_center_quotient
    m K ⟨Nat.prime_three, le_rfl, hm, ?_⟩ (by rw [pow_one]; exact hK)⟩
  intro h
  simp only [Prod.mk.injEq] at h
  omega

theorem blockData_statedSp
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {m : ℕ} (hm : 2 ≤ m) :
    BlockData ↥(StatedSp m K) := by
  have hL := lieModel_quotient_statedSp hK hm
  have hZ := card_center_statedSp_three hK (by omega : 1 ≤ m)
  refine ⟨?_, ⟨1, le_rfl, by rw [hZ, pow_one]⟩, ⟨.PSp, m, hL, Or.inr (Or.inr (Or.inl ⟨rfl, hm⟩))⟩,
    ?_⟩
  · exact LieType.Universal.Symplectic.isQuasisimple m K (by omega)
      (Or.inr (Or.inl ⟨hK, hm⟩))
  · have hfac := factorization_card_griessHopfMultiplier_psp hGA (p := 3) (f := 1)
      (by norm_num) (by omega) hL
    rw [hfac, hZ]
    simp

end CFSG.OddStandard.HigherRank.F3
