module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightAut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightRoot
public import Certificates.Certificate43
public import Certificates.Certificate113
public import CFSG.GH74.Statements
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.JOneRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.NonSquare
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankBound
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Remaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.WalterRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.TheoremC
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
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

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ProperTwoGeneratedCore.TheoremC
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)} [J.Normal]

structure IsInnerPart (hz : IsCentralInvolution (S : Subgroup G) z)
    (φ : (S : Subgroup G) →* J ⧸ Subgroup.center J) : Prop where
  mem_sylow : ∀ s, φ s ∈ (sylowStar hz J : Subgroup (J ⧸ Subgroup.center J))
  eq_mk : ∀ s (h : sylowBar hz s ∈ J), φ s = ((⟨sylowBar hz s, h⟩ : J) : J ⧸ Subgroup.center J)
  mem_centralizer : ∀ s, φ s = 1 →
    sylowBar hz s ∈ Subgroup.centralizer (J : Set (EscapingQuotient z))

namespace IsInnerPart

variable {hz : IsCentralInvolution (S : Subgroup G) z}
  {φ : (S : Subgroup G) →* J ⧸ Subgroup.center J} (hφ : IsInnerPart hz φ)
include hφ

theorem exists_eq {r : J ⧸ Subgroup.center J}
    (hr : r ∈ (sylowStar hz J : Subgroup (J ⧸ Subgroup.center J))) :
    ∃ q : (S : Subgroup G), ∃ h : sylowBar hz q ∈ J, φ q = r ∧
      ((⟨sylowBar hz q, h⟩ : J) : J ⧸ Subgroup.center J) = r := by
  obtain ⟨v, hvS, rfl⟩ := exists_mk_eq_of_mem_sylowStar hz hr
  rw [← sylowBar_range hz] at hvS
  obtain ⟨q, hq⟩ := hvS
  have hqJ : sylowBar hz q ∈ J := hq ▸ v.2
  refine ⟨q, hqJ, ?_, ?_⟩ <;> rw [← show (⟨sylowBar hz q, hqJ⟩ : J) = v from Subtype.ext hq]
  exact hφ.eq_mk q hqJ

theorem exists_mul (s : (S : Subgroup G)) :
    ∃ q : (S : Subgroup G), ∃ _ : sylowBar hz q ∈ J, φ q = φ s ∧
      sylowBar hz (q⁻¹ * s) ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
  obtain ⟨q, hqJ, hq, -⟩ := hφ.exists_eq (hφ.mem_sylow s)
  refine ⟨q, hqJ, hq, hφ.mem_centralizer _ ?_⟩
  rw [map_mul, map_inv, hq, inv_mul_cancel]

end IsInnerPart

namespace SzEightSetting

variable (hs : SzEightSetting S H z J)
include hs

omit [J.Normal] in
theorem center_quotient_eq_bot : Subgroup.center (J ⧸ Subgroup.center J) = ⊥ := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hs.component.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (J ⧸ Subgroup.center J)) with
    h | h
  · exact h
  · exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)) hab

omit [J.Normal] in
theorem isPGroup_sylowImage : IsPGroup 2 (escapingSylowImage S z) := by
  have h := (sylowBarSylow hs.central).isPGroup'
  rwa [coe_sylowBarSylow, sylowBar_range] at h

variable (e : (J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1))
include e

omit [Finite G] [J.Normal] hs in
theorem odd_card_outer :
    Odd (Nat.card (Outer (J ⧸ Subgroup.center J))) :=
  odd_card_outer_of_mulEquiv_suzukiMatrixGroup le_rfl
    (e.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup 1)))

theorem sylowFacts :
    SzEightSylowFacts (sylowStar hs.central J : Subgroup (J ⧸ Subgroup.center J)) :=
  szEightSylowFacts_of_mulEquiv e _

theorem exists_isInnerPart :
    ∃ φ : (S : Subgroup G) →* J ⧸ Subgroup.center J,
    IsInnerPart hs.central φ := by
  have hmem : ∀ s : (S : Subgroup G), sylowBar hs.central s ∈ escapingSylowImage S z :=
    fun s => by
      rw [← sylowBar_range hs.central]
      exact ⟨s, rfl⟩
  set P := escapingSylowImage S z
  set ψ := innerPart (odd_card_outer e) hs.center_quotient_eq_bot P hs.isPGroup_sylowImage
  let ι : (S : Subgroup G) →* P := (sylowBar hs.central).codRestrict P hmem
  have hψJ : ∀ (w : P) (h : (w : EscapingQuotient z) ∈ J), ψ w = ((⟨w, h⟩ : J) : J ⧸ _) :=
    fun w h => innerPart_eq_mk _ _ _ _ w h
  have hQ : (sylowStar hs.central J : Subgroup (J ⧸ Subgroup.center J)) ≤ ψ.range := by
    intro r hr
    obtain ⟨v, hvS, rfl⟩ := exists_mk_eq_of_mem_sylowStar hs.central hr
    exact ⟨⟨v, hvS⟩, hψJ ⟨v, hvS⟩ v.2⟩
  refine ⟨ψ.comp ι, fun s => innerPart_mem_sylow _ _ _ _ _ hQ (ι s), fun s h => hψJ (ι s) h,
    fun s h => mem_centralizer_of_innerPart_eq_one (odd_card_outer e) hs.center_quotient_eq_bot P
      hs.isPGroup_sylowImage hs.commutator_eq_top (ι s) h⟩

theorem mul_self_eq_one_of_inCenterOf'
    {w : J}
    (hwc : InCenterOf ((sylowJ hs.central J : Subgroup J).map (QuotientGroup.mk' _))
      (w : J ⧸ Subgroup.center J)) : w * w = 1 := by
  obtain ⟨x, hxQ, hxx, hxZ⟩ := hs.exists_involution_sylowJ
  have hxS : (x : J ⧸ Subgroup.center J) ∈
      (sylowStar hs.central J : Subgroup (J ⧸ Subgroup.center J)) := by
    rw [coe_sylowStar]
    exact ⟨x, hxQ, rfl⟩
  refine hs.mul_self_eq_one_of_inCenterOf hxx hxZ ⟨by rw [← coe_sylowStar]; exact hxS,
    fun q hq => ?_⟩ hwc
  rw [← coe_sylowStar] at hq
  have h := (hs.sylowFacts e).comm_of_sq ⟨_, hxS⟩ (Subtype.ext (by
    rw [Subgroup.coe_pow, pow_two, ← QuotientGroup.mk_mul, hxx, QuotientGroup.mk_one]; rfl))
    ⟨q, hq⟩
  exact (congrArg Subtype.val h).symm

theorem inCenterOf_of_sq_eq_one {r : J ⧸ Subgroup.center J}
    (hr : r ∈ (sylowStar hs.central J : Subgroup (J ⧸ Subgroup.center J))) (hrr : r * r = 1) :
    InCenterOf ((sylowJ hs.central J : Subgroup J).map (QuotientGroup.mk' _)) r := by
  rw [← coe_sylowStar]
  refine ⟨hr, fun q hq => ?_⟩
  have h := (hs.sylowFacts e).comm_of_sq ⟨r, hr⟩ (Subtype.ext (by
    rw [Subgroup.coe_pow, pow_two]; exact hrr)) ⟨q, hq⟩
  exact (congrArg Subtype.val h).symm

theorem mul_self_ne_bar
    {q : J} (hq : q ∈ (sylowJ hs.central J : Subgroup J)) :
    (q * q : J) ≠ ⟨escapingBar z, hs.bar_mem⟩ := by
  intro h
  have hqq : ((q : J ⧸ Subgroup.center J)) * q = 1 := by
    rw [← QuotientGroup.mk_mul, h, QuotientGroup.eq_one_iff, hs.mem_center_iff]
    exact Or.inr rfl
  have hqS : (q : J ⧸ Subgroup.center J) ∈
      (sylowStar hs.central J : Subgroup (J ⧸ Subgroup.center J)) := by
    rw [coe_sylowStar]
    exact ⟨q, hq, rfl⟩
  have h1 := hs.mul_self_eq_one_of_inCenterOf' e (hs.inCenterOf_of_sq_eq_one e hqS hqq)
  rw [h1] at h
  have h2 := congrArg Subtype.val h
  have h3 := hs.quotientData.bar_order
  rw [← show (1 : EscapingQuotient z) = escapingBar z from h2, orderOf_one] at h3
  exact absurd h3 (by decide)

omit e in
theorem mem_sylowJ_sylowBar {q : (S : Subgroup G)} (hqJ : sylowBar hs.central q ∈ J) :
    (⟨_, hqJ⟩ : J) ∈ (sylowJ hs.central J : Subgroup J) := by
  rw [mem_sylowJ_iff, ← sylowBar_range hs.central]
  exact ⟨q, rfl⟩

theorem inCenterOf_of_mul_self
    {φ : (S : Subgroup G) →* J ⧸ Subgroup.center J}
    (hφ : IsInnerPart hs.central φ) {s : (S : Subgroup G)} (hss : s * s = 1) :
    ∃ h : sylowBar hs.central s ∈ J,
      InCenterOf ((sylowJ hs.central J : Subgroup J).map (QuotientGroup.mk' _))
        ((⟨_, h⟩ : J) : J ⧸ Subgroup.center J) := by
  obtain ⟨q, hqJ, -, hk⟩ := hφ.exists_mul s
  set k := sylowBar hs.central (q⁻¹ * s) with hkdef
  have hsqk : sylowBar hs.central s = sylowBar hs.central q * k := by
    rw [hkdef, map_mul, map_inv, mul_inv_cancel_left]
  have hcomm : sylowBar hs.central q * k = k * sylowBar hs.central q :=
    Subgroup.mem_centralizer_iff.mp hk _ hqJ
  have h1 : sylowBar hs.central s * sylowBar hs.central s = 1 := by
    rw [← map_mul, hss, map_one]
  have hq2k2 : sylowBar hs.central q * sylowBar hs.central q * (k * k) = 1 := by
    rw [← h1, hsqk]
    calc sylowBar hs.central q * sylowBar hs.central q * (k * k)
        = sylowBar hs.central q * (sylowBar hs.central q * k) * k := by group
      _ = sylowBar hs.central q * (k * sylowBar hs.central q) * k := by rw [hcomm]
      _ = sylowBar hs.central q * k * (sylowBar hs.central q * k) := by group
  have hqqC : sylowBar hs.central q * sylowBar hs.central q ∈
      Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    rw [eq_inv_of_mul_eq_one_left hq2k2]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hk hk)
  have hqqZ : (⟨_, hqJ⟩ * ⟨_, hqJ⟩ : J) ∈ Subgroup.center J := mem_center_of_mem_centralizer hqqC
  have hqq1 : sylowBar hs.central q * sylowBar hs.central q = 1 := by
    rcases hs.center _ hqqZ with h | h
    · exact h
    · exact absurd (Subtype.ext h) (hs.mul_self_ne_bar e (hs.mem_sylowJ_sylowBar hqJ))
  have hkk : k * k = 1 := by rwa [hqq1, one_mul] at hq2k2
  have hkJ : k ∈ J ∧ ∀ hk' : k ∈ J, (⟨k, hk'⟩ : J) ∈ Subgroup.center J := by
    by_cases hk1 : k = 1
    · rw [hk1]
      exact ⟨J.one_mem, fun _ => Subgroup.one_mem _⟩
    · have hk2 : orderOf k = 2 := orderOf_eq_prime (by rw [pow_two]; exact hkk) hk1
      rw [hs.eq_bar_of_mem_centralizer hk hk2]
      exact ⟨hs.bar_mem, fun h => (hs.mem_center_iff _).mpr (Or.inr rfl)⟩
  have hsJ : sylowBar hs.central s ∈ J := hsqk ▸ J.mul_mem hqJ hkJ.1
  refine ⟨hsJ, ?_⟩
  have hmk : ((⟨_, hsJ⟩ : J) : J ⧸ Subgroup.center J) = ((⟨_, hqJ⟩ : J) : J ⧸ _) := by
    rw [QuotientGroup.eq]
    have h : (⟨_, hsJ⟩ : J)⁻¹ * ⟨_, hqJ⟩ = (⟨k, hkJ.1⟩ : J)⁻¹ := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hsqk]
      group)
    rw [h]
    exact Subgroup.inv_mem _ (hkJ.2 hkJ.1)
  rw [hmk]
  refine hs.inCenterOf_of_sq_eq_one e ?_ ?_
  · rw [coe_sylowStar]
    exact ⟨_, hs.mem_sylowJ_sylowBar hqJ, rfl⟩
  · rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, show (⟨_, hqJ⟩ * ⟨_, hqJ⟩ : J) = 1 from
      Subtype.ext hqq1]
    exact Subgroup.one_mem _

end SzEightSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
