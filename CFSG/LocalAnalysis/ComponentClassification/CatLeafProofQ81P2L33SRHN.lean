module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon
public import CFSG.Sporadic.HN
public import CFSG.Sporadic.Co2Schreier.OddCore
public import CFSG.Sporadic.HNOddCore.Fusion
public import CFSG.Sporadic.HNOddCore.ThreeInvol
public import CFSG.Sporadic.HNOddCore.OuterFix
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2086
public import Certificates.Certificate2087
public import Certificates.Certificate2088
public import Certificates.Certificate2089
public import Certificates.Certificate2090
public import Certificates.Certificate2091
public import Certificates.Certificate2093
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2098
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2103
public import Certificates.Certificate2104
public import Certificates.Certificate2107
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate3166
public import Certificates.Certificate16041
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
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

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore

theorem not_isPGroup_of_card_eq {G : Type*} [Group G] [Finite G] {n : ℕ} (h : Nat.card G = n)
    (h3 : 3 ∣ n) : ¬ IsPGroup 2 G :=
  not_isPGroup_of_three_dvd (h ▸ h3)

theorem hn_centralizer_not_isPGroup
    {Y : Type} [Group Y] (e' : Y ≃* JH) (t : Y) (ht : orderOf t = 2) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set Y)) := by
  have hs : orderOf (e' t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  have hs2 : (jR (e' t)) ^ 2 = 1 := by rw [← map_pow, ← hs, pow_orderOf_eq_one, map_one]
  have hs1 : jR (e' t) ≠ 1 := fun h1 => by
    have h0 : e' t = 1 := jR_injective (h1.trans (map_one jR).symm)
    rw [h0, orderOf_one] at hs
    norm_num at hs
  obtain ⟨hcov, -, -, -, hreal, -, -, -, -, -, -, -, hc2, -, -⟩ :=
    ctuc_hn_involution_fusion_and_local_stabilizers
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc4, -⟩ :=
    ctuc_hn_three_involution_centralizers_exact
  have key : ∀ r : JH, IsConj (jR r) (jR (e' t)) → ¬ IsPGroup 2 ↥(centralizer ({r} : Set JH)) →
      ¬ IsPGroup 2 ↥(centralizer ({t} : Set Y)) := by
    intro r hr hnr
    obtain ⟨g, hg⟩ := hreal _ _ hs2 hs1 hr.symm
    have hg' : g * e' t * g⁻¹ = r := jR_injective (by rw [map_mul, map_mul, map_inv]; exact hg)
    have h1 : ¬ IsPGroup 2 ↥(centralizer ({e' t} : Set JH)) :=
      not_isPGroup_centralizer_of_isConj
        ((@isConj_iff _ (Subgroup.toGroup _) _ _).mpr ⟨g, hg'⟩).symm hnr
    exact @not_isPGroup_of_mulEquiv _ _ _ (Subgroup.toGroup _)
      (@CFSG.Sporadic.Co2Schreier.centralizerMap Y _ _ (Subgroup.toGroup _) e' t) h1
  rcases hcov _ hs2 hs1 with h | h | h
  · exact absurd h (not_isConj_c_jR (e' t))
  · exact key _ h (not_isPGroup_of_card_eq hc2 (by norm_num))
  · exact key _ h (not_isPGroup_of_card_eq hc4 (by norm_num))

theorem sporNoTwoFix_HN :
    SporNoTwoFix .HN := by
  intro Y _ _ ⟨e⟩ α hα
  have hsY : IsSimpleGroup Y :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HN.isSimpleGroup_HN e
  have hZ : center Y = ⊥ := center_eq_bot_of_not_prime hsY
    ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HN.card_HN) (by norm_num)
  by_cases hin : α ∈ OuterAutomorphisms.inner Y
  · obtain ⟨t, rfl⟩ := hin
    exact not_isPGroup_fixedPoints_conj hZ
      (hn_centralizer_not_isPGroup (e.trans hnEquivJ)) hα
  · obtain ⟨f⟩ := hn_outer_involution_fixSub e α hα hin
    rw [← Hin.fixSub_eq_fixedPoints]
    refine not_isPGroup_of_mulEquiv f (not_isPGroup_of_three_dvd ?_)
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide

end CFSG.ComponentClassification.HarrisLit.L33.SR
