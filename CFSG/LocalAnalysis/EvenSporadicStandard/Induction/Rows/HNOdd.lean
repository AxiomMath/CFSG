module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OddCoreBridge
public import CFSG.Sporadic.HNOddCore.AlmostSimple
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance
public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.ThSchreier.AutCore
public import Certificates.Certificate3085Base

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier
  CFSG.Sporadic.HNOddCore

section Fixed


theorem map_fixSubgroup_conjR (ν : MulAut ↥JH) (r : RH) (hr : conjR r = ν) :
    Subgroup.map jR (fixSubgroup ν : Subgroup ↥JH) = jR.range ⊓ Subgroup.centralizer {r} := by
  have hfix : ∀ j : ↥JH, ν j = j ↔ jR j * r = r * jR j := fun j => by
    rw [← hr]
    exact conjR_fix_iff r j
  ext p
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, rfl⟩, (hfix j).1 hj⟩
  · rintro ⟨⟨j, rfl⟩, hp⟩
    exact ⟨j, (hfix j).2 hp, rfl⟩

end Fixed

section Model


theorem jhAutOddCore : AutOddCoreTrivial ↥JH := by
  refine autOddCoreTrivial_of_oddCore fun ν hν1 hνν => ?_
  obtain ⟨r, hr⟩ := conjR_surjective ν
  have hr2 : r ^ 2 = 1 := conjR_injective (by rw [map_pow, pow_two, hr, hνν, map_one])
  have hr1 : r ≠ 1 := fun h => hν1 (by rw [← hr, h, map_one])
  have hB : CFSG.oddCore ↥(jR.range ⊓ Subgroup.centralizer {r}) = ⊥ :=
    oddCore_inf_normal_bot range_jR_normal (oddCore_CR_of_involution hr2 hr1)
  refine oddCore_bot_of_mulEquiv ?_ hB
  exact (Subgroup.equivMapOfInjective (fixSubgroup ν : Subgroup ↥JH) jR jR_injective).trans
    (MulEquiv.subgroupCongr (map_fixSubgroup_conjR ν r hr))

theorem hnOddCore : HNOddCore :=
  @AutOddCoreTrivial.of_mulEquiv NativeSporadic.HN ↥JH _ _ hnEquivJ jhAutOddCore

end Model

end CFSG.EvenSporadicStandard.Induction
