module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1Perfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1Center
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1TwoB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOne
public import CFSG.Sporadic.Schreier.Co1OddCore
public import CFSG.Sporadic.Co2Schreier.OddCore
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.StandardCentralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance
public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import Certificates.Certificate3085Base

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoCo1.HypOne

theorem autOddCoreTrivial_of_allInner_oddCore {Y : Type} [Group Y]
    (hinn : ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g)
    (hZ : center Y = ⊥)
    (h : ∀ t : Y, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set Y)) = ⊥) :
    AutOddCoreTrivial Y := by
  intro ν hν1 hνν P hP hPn hodd
  obtain ⟨g, rfl⟩ := hinn ν
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hν1 (map_one _)
  have hg2 : g ^ 2 = 1 := by
    have hc : g * g ∈ center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun f : MulAut Y => f y) hνν
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at this
      calc y * (g * g) = (g * (g * y * g⁻¹) * g⁻¹) * (g * g) := by rw [this]
        _ = g * g * y := by group
    rw [hZ, Subgroup.mem_bot] at hc
    rw [pow_two]
    exact hc
  have hord : orderOf g = 2 := orderOf_eq_prime hg2 hg1
  rw [fixSubgroup_conj g] at hP hPn
  have hle : P.subgroupOf (centralizer ({g} : Set Y)) ≤
      CFSG.oddCore ↥(centralizer ({g} : Set Y)) :=
    le_sSup ⟨hPn, by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv]⟩
  rw [h g hord, le_bot_iff] at hle
  refine eq_bot_iff.2 fun x hx => ?_
  have hx' : (⟨x, hP hx⟩ : ↥(centralizer ({g} : Set Y))) ∈
      P.subgroupOf (centralizer ({g} : Set Y)) := hx
  rw [hle, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')

theorem center_eq_bot_of_isSimple_nonabelian {Y : Type} [Group Y] (hs : IsSimpleGroup Y)
    (hnc : ∃ a b : Y, a * b ≠ b * a) : center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)

theorem co1_involution_oddCore
    (b : CFSG.Blueprint.NativeSporadic.Co1) (hb : orderOf b = 2) :
    CFSG.oddCore (centralizer ({b} : Set CFSG.Blueprint.NativeSporadic.Co1)) = ⊥ := by
  have hCo2odd : ∀ a : CFSG.Sporadic.Co2Cert.co2P, orderOf a = 2 →
      CFSG.oddCore (centralizer ({a} : Set CFSG.Sporadic.Co2Cert.co2P)) = ⊥ :=
    fun a ha => CFSG.Sporadic.Co2Schreier.CTUC_Co2_all_involution_centralizers_odd_core_free a ha
  exact (CFSG.Sporadic.Co1Schreier.OddCore.all_involution_centralizers_odd_core_free_of_inputs
    hCo2odd b hb).2.2.2

theorem perfectRowData_co1
    : PerfectRowData .Co1 where
  allInner _ _ h := allInner_of_isSporadic h
  perfect Y _ h := by
    obtain ⟨e⟩ := h
    exact PerfectInvolutions.of_mulEquiv e.symm (perfectInvolutions_native a₁_mem_commutator)
  center Y _ h := by
    obtain ⟨e⟩ := h
    exact CenterInvolutions.of_mulEquiv e.symm centerInvolutions_native
  oddCore Y _ h := by
    obtain ⟨e⟩ := h
    exact autOddCoreTrivial_of_allInner_oddCore (allInner_of_isSporadic ⟨e⟩)
      (center_eq_bot_of_isSimple_nonabelian (co1_isSimpleGroup_of_isSporadic ⟨e⟩)
        (co1_exists_not_commute ⟨e⟩))
      (oddCore_free_of_mulEquiv' e fun b hb => co1_involution_oddCore b hb)

end CFSG.EvenSporadicStandard.Induction
