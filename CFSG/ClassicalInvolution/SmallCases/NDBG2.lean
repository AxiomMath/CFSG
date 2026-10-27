module

public import CFSG.ClassicalInvolution.SmallCases.NDBG1
public import CFSG.ClassicalInvolution.SmallCases.NDBF
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreTight
public import CFSG.ClassicalInvolution.Asc77.AscT3Final
public import CFSG.ClassicalInvolution.Asc77.AscBSCMain
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedMain
public import CFSG.ClassicalInvolution.RouteD.G2D4T3Free
public import CFSG.GH74.GLS.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.StronglyEmbedded.UniqueCoset

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.AS76b (Asc75Theorem4)

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

section Core

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem aEmpty_of_omegaOfSet_nonempty (h95 : L9_5Mod p f) (h4 : Asc75Theorem4)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hL : (omegaOfSet (𝒞 K) (twinSet (𝒞 K) K)).Nonempty) : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := by
  have hΩ : HypOmegaMod p f (𝒞 K) := Cover.hypOmegaMod hnab hp2 hq hz hBelow
  have hK : K ∈ 𝒞 K := mem_conjClass_self K
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have htrans : ∀ J ∈ 𝒞 K, ∃ g : G, conjSub g K = J := by
    rintro J ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hA : AEmpty (𝒞 K) K := by
    by_contra hn
    obtain ⟨J, zK, zJ, hv⟩ := T3.not_aEmpty_iff.mp hn
    have hzK : zK = z := hv.hzK.eq hKz
    subst hzK
    obtain ⟨L, hLs⟩ := hL
    obtain ⟨l, hl⟩ := hΩ.classical L hLs.1
    have hlU : IsUniqueInvolution L l :=
      ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hl
    have hne : T3.aStar (𝒞 K) K ≠ 𝒞 K :=
      NDBG.aStar_ne_of_mem_omegaOfSet hp2 hq hΩ hK (h95 G hnab hp2 hq K zK hz hBelow) hLs hlU
    exact T3Core.caseI_false hp2 hq h4 hnab hΩ hK hv htrans hBelow hne
  exact T3.aEmpty_forall_of_transitive' hΩ.conjInvariant htrans hA

theorem false_of_g2_of_card (h95 : L9_5Mod p f) (h4 : Asc75Theorem4)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) {b : Fin D.card} (hG2 : D.tag b = .G2)
    (hcard : 3 ≤ D.card) : False := by
  let C := Cover.toXCtx hnab hp2 hq hz hBelow D
  have hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := fun h => by
    rw [show C.D.tag b = .G2 from hG2] at h
    exact absurd h.1 (by decide)
  obtain ⟨N, hN, n, hn, hnz⟩ := NDBG.exists_far_member (C := C) hno hb
  have hNs : N ∈ omegaOfSet (𝒞 K) (twinSet (𝒞 K) K) :=
    NDBG.mem_omegaOfSet_of_tq hp2 hq C.hΩ (mem_conjClass_self K) C.hKz hN hn hnz
  have hA := aEmpty_of_omegaOfSet_nonempty h95 h4 hnab hp2 hq hz hBelow ⟨N, hNs⟩
  exact BSC.BSE.false_of_g2_of_aEmpty (C := C) hno (b := b) hG2 hcard hA

end Core

section Residuals

theorem noG2D4Twin_of (h95 : L9_5Mod p f) (h4 : Asc75Theorem4) : NoG2D4Twin p f := by
  intro G _ _ _ K z hS hT D i hi
  have hno := fuzzyFrameExcluded G K z hS
  let C := Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
  have hb : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2) := fun h => by
    rcases hi with hi | hi <;>
    · rw [show C.D.tag i = _ from hi] at h
      exact absurd h.1 (by decide)
  obtain ⟨T, hTΩ, hTK, hTz⟩ := hT
  have hcard : 3 ≤ C.D.card := NDBG.three_le_card_of_twin C hb hTΩ hTK hTz
  rcases hi with hG2 | hD4
  · exact false_of_g2_of_card h95 h4 hS.nonabelian hS.odd hS.five hS.member hS.below hno D hG2
      hcard
  · exact NDBG.false_of_trialityD4_of_card (C := C) hno (b := i) hD4 hcard

theorem bootNoG2Twin_of (h95 : L9_5Mod p f) (h4 : Asc75Theorem4) : BSC.BootNoG2Twin p f := by
  intro G _ _ _ K z hS D i hG2 hcard
  exact false_of_g2_of_card h95 h4 hS.nonabelian hS.odd hS.five hS.member hS.below
    (BSC.noFuzzyFrame hS) D hG2 hcard

theorem bootNoG2TwinThree_of (h95 : L9_5Mod p f) (h4 : Asc75Theorem4) :
    BSC.BootNoG2TwinThree p f := by
  intro G _ _ _ K z hS D i hG2 hcard
  exact bootNoG2Twin_of h95 h4 G K z hS D i hG2 (by omega)

theorem aEmptyG2Twin_of (h95 : L9_5Mod p f) (h4 : Asc75Theorem4) : BSC.AEmptyG2Twin p f := by
  intro G _ _ _ K z hS D i hG2 hcard
  let C := Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
  have hb : ¬ (C.D.tag i = .PSL ∧ C.D.rank i = 2) := fun h => by
    rw [show C.D.tag i = .G2 from hG2] at h
    exact absurd h.1 (by decide)
  obtain ⟨N, hN, n, hn, hnz⟩ := NDBG.exists_far_member (C := C) (BSC.noFuzzyFrame hS) hb
  have hNs : N ∈ omegaOfSet (𝒞 K) (twinSet (𝒞 K) K) :=
    NDBG.mem_omegaOfSet_of_tq hS.odd hS.five C.hΩ (mem_conjClass_self K) C.hKz hN hn hnz
  exact aEmpty_of_omegaOfSet_nonempty h95 h4 hS.nonabelian hS.odd hS.five hS.member hS.below
    ⟨N, hNs⟩

end Residuals

end CFSG.ClassicalInvolution.NDB
