module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2
import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot
import CFSG.ClassicalInvolution.AschTight.HypOmegaGenMod
import CFSG.ClassicalInvolution.AschTight.Sec6Gen64O
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndBasic
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.AschTight.Thm6Tight
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
import CFSG.ClassicalInvolution.Asc77.AscE184Basic
import CFSG.ClassicalInvolution.Asc77.AscSixZW
import CFSG.Goldschmidt.Statements
import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.StatementsX
import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

theorem hypOmegaGen_of_commute {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hconj : ConjInvariant Ω) (hinv : ∀ K ∈ Ω, ∃ z : G, IsUniqueInvolution K z)
    (hcen : ∀ K ∈ Ω, ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x * x = 1)
    (hsyl : ∀ K ∈ Ω, ∃ P : Subgroup G, IsSylow2In P K ∧ ¬ IsMulCommutative ↥P)
    (hgen : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} = K ∨
      Nonempty (↥K ⧸ CFSG.Open.classicalInvolutionOddCore ↥K ≃* SL(2, ZMod 3)))
    (hcard : ∀ K ∈ Ω, ∀ J ∈ Ω, ∀ P Q : Subgroup G, IsSylow2In P K → IsSylow2In Q J →
      Nat.card ↥P = Nat.card ↥Q)
    (hcomm : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → 2 ∣ Nat.card ↥(K ⊓ J) → ⁅K, J⁆ = ⊥)
    (hnorm : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
      (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
        v ∈ Subgroup.normalizer (K : Set G)) :
    HypOmegaGen Ω where
  conjInvariant := hconj
  omega1 K hK := ⟨hinv K hK, hsyl K hK⟩
  omega2 := hgen
  omega3 := hcard
  omega4 K hK J hJ hne := by
    obtain ⟨z, hz⟩ := hinv K hK
    by_cases h2 : 2 ∣ Nat.card ↥(K ⊓ J)
    · have hcm : ⁅K, J⁆ = ⊥ := hcomm K hK J hJ hne h2
      have hJK : J ≤ Subgroup.centralizer (K : Set G) := by
        refine Subgroup.commutator_eq_bot_iff_le_centralizer.mp ?_
        rwa [Subgroup.commutator_comm]
      have hle : K ⊓ J ≤ Subgroup.zpowers z := by
        intro x hx
        have hxK : x ∈ K := (Subgroup.mem_inf.mp hx).1
        have hxJ : x ∈ J := (Subgroup.mem_inf.mp hx).2
        have hxc : ∀ y ∈ K, x * y = y * x := by
          have hx' : x ∈ Subgroup.centralizer (K : Set G) := hJK hxJ
          rw [Subgroup.mem_centralizer_iff] at hx'
          exact fun y hy => (hx' y hy).symm
        rcases hz.unique x hxK (hcen K hK x hxK hxc) with h1 | hz'
        · rw [h1]
          exact Subgroup.one_mem _
        · rw [hz']
          exact Subgroup.mem_zpowers z
      have hcard2 : Nat.card ↥(K ⊓ J) ≤ 2 :=
        calc Nat.card ↥(K ⊓ J) ≤ Nat.card ↥(Subgroup.zpowers z) :=
              Subgroup.card_le_of_le hle
          _ = orderOf z := Nat.card_zpowers z
          _ = 2 := orderOf_eq_prime (by simpa [pow_two] using hz.sq) hz.ne_one
      have hle1 : padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 := by
        by_contra hle'
        have h2le : 2 ≤ padicValNat 2 (Nat.card ↥(K ⊓ J)) := by omega
        have h4 : 4 ∣ Nat.card ↥(K ⊓ J) := by
          have h := (padicValNat_dvd_iff_le (p := 2) (a := Nat.card ↥(K ⊓ J)) (n := 2)
            Nat.card_pos.ne').mpr h2le
          simpa using h
        have h4le := Nat.le_of_dvd Nat.card_pos h4
        omega
      exact ⟨hle1, fun _ => by rw [hcm]; exact bot_le⟩
    · rw [padicValNat.eq_zero_of_not_dvd h2]
      exact ⟨Nat.zero_le _, fun h => absurd h (by norm_num)⟩
  omega5 := hnorm

end CFSG.ClassicalInvolution.Disconnected.AschTight
