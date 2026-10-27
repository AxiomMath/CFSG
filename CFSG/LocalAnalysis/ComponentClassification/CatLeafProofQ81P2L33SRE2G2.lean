module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2Open
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE2Tools
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenShortCentralizer
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Leaf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC311a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCor441
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Fbar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitProperComplete
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate3085Base

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog

variable {K : Type} [Field K]

theorem g2_not_isPGroup_of_sl2
    [CharP K 2] {x : adjointGroup .G2 K} (ρ : SL2 K →* ModGL .G2 K)
    (hρ : Function.Injective ρ)
    (hmem : ∀ s, ρ s ∈ adjointGroup .G2 K ⊓ centralizer ({(x : ModGL .G2 K)} : Set (ModGL .G2 K))) :
    ¬ IsPGroup 2 ↥(centralizer ({x} : Set (adjointGroup .G2 K))) := by
  refine not_isPGroup_of_sl2 (ρ.codRestrict (adjointGroup .G2 K) fun s => (hmem s).1)
    (fun a b h => hρ (congrArg Subtype.val h)) fun s => Subtype.ext ?_
  exact mem_centralizer_singleton_iff.mp (hmem s).2

theorem g2_centralizer_not_isPGroup
    [Finite K] [CharP K 2] {z : adjointGroup .G2 K} (hz : orderOf z = 2) :
    ¬ IsPGroup 2 ↥(centralizer ({z} : Set (adjointGroup .G2 K))) := by
  rcases even_G2_involutions_conjugate_to_root_elements K (ringChar.eq K 2) z hz with h | h
  · refine not_isPGroup_centralizer_of_isConj h.symm ?_
    obtain ⟨-, -, -, hcent, -, -, -, ⟨ρ, -, -, hρr, hρi⟩, -⟩ :=
      even_G2_highest_long_root_centralizer K
    refine g2_not_isPGroup_of_sl2 ρ hρi fun s => ?_
    show ρ s ∈ adjointGroup .G2 K ⊓ centralizer ({pinnedX .G2 K g2c 1} : Set (ModGL .G2 K))
    rw [hcent]
    exact Subgroup.mem_sup_right (hρr ▸ (⟨s, rfl⟩ : ρ s ∈ ρ.range))
  · refine not_isPGroup_centralizer_of_isConj h.symm ?_
    obtain ⟨-, -, -, hcent, -, -, -, ⟨ρ, -, -, hρr, hρi⟩, -⟩ :=
      even_G2_highest_short_root_centralizer K
    refine g2_not_isPGroup_of_sl2 ρ hρi fun s => ?_
    show ρ s ∈ adjointGroup .G2 K ⊓ centralizer ({pinnedX .G2 K g2v 1} : Set (ModGL .G2 K))
    rw [hcent]
    exact Subgroup.mem_sup_right (hρr ▸ (⟨s, rfl⟩ : ρ s ∈ ρ.range))

end CFSG.ComponentClassification.HarrisLit.L33.SR.E2

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem involutionCentralizerNotTwoGroup_G2
    : InvolutionCentralizerNotTwoGroup .G2 := by
  intro Y _ _ f hY _ c hc
  obtain ⟨⟨-, hf, -⟩, hm⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact SR.E2.not_isPGroup_of_mulEquiv e c
    (SR.E2.g2_centralizer_not_isPGroup (by rw [MulEquiv.orderOf_eq]; exact hc))

end CFSG.ComponentClassification.HarrisLit.L33.E2
