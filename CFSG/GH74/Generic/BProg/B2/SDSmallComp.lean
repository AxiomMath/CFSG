module

public import CFSG.GH74.Generic.BProg.B2.SDOrders
public import CFSG.GH74.Generic.BProg.B2.SDRank
public import CFSG.GH74.E2.CompCerts
public import CFSG.GH74.Generic.NativeCerts
import CFSG.GH74.Generic.AltCerts
import CFSG.GH74.Generic.BProg.B1.Stage3aRankJ1
import CFSG.GH74.Generic.BProg.B1.Stage3aRankRee
import CFSG.GH74.Generic.BProg.B2.Thm2Comp
import CFSG.GH74.Generic.ClassicalCerts
import CFSG.GH74.Generic.Context
import CFSG.GH74.Generic.ExceptionalRank
import CFSG.GH74.Generic.GKFRank3D4
import CFSG.GH74.Generic.S3.Front
import CFSG.GH74.Generic.Sections
import CFSG.Walter.Models
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
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
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.Generic.BProg.B1.Lift0
public import CFSG.GH74.Generic.BProg.B2.Lemma82
public import CFSG.GH74.Generic.BProg.Stage2Frozen
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
public import Certificates.Certificate5007
public import Certificates.Certificate5125

public section

namespace CFSG.GH74.Generic.BProg.B2.SD2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

namespace SDSmallComp

theorem three_le_prime_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) : 3 ≤ p ^ f := by
  have h2 := hp.two_le
  have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  omega

theorem odd_prime_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Odd (p ^ f) :=
  (hp.odd_of_ne_two hp2).pow

theorem three_lt_or_eq {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    (p = 3 ∧ f = 1) ∨ 3 < p ^ f := by
  by_cases hq3 : p ^ f = 3
  · exact Or.inl (CFSG.GH74.Generic.eq_three_of_pow_eq_three hp hf hq3)
  · have := three_le_prime_pow hp hp2 hf
    exact Or.inr (by omega)

theorem prime_ne_two_of_pow_mod_four {p f : ℕ} (hf : 1 ≤ f) {r : ℕ} (hr : r = 1 ∨ r = 3)
    (h : p ^ f % 4 = r) : p ≠ 2 := by
  rintro rfl
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
  rw [pow_succ] at h
  omega

theorem rankCertified_of_isSporadic_J1 {S : Type} [Group S]
    (h : NativeSporadic.IsSporadic S .J1) : RankCertified S 2 := by
  obtain ⟨e0⟩ := h
  exact B1.rankCertified_walterJ1_two.of_mulEquiv
    (e0.trans CFSG.Walter.walterJ1EquivNative.symm).symm

theorem smallComp_of_ghList
    {J : Type} [Group J] [Finite J] (hr : SectionalTwoRankLE J 2)
    (hgh : GHList (J ⧸ center J)) : SmallComp J := by
  have F2 : RankCertified (J ⧸ center J) 2 → False := fun hc =>
    (hc.of_quotient (center J)).not_sectionalTwoRankLE hr
  have F3 : RankCertified (J ⧸ center J) 3 → False := fun hc => F2 (hc.mono (by norm_num))
  rcases hgh with ⟨n, hn7, hn11, ⟨e⟩⟩ | hsp | ⟨p, f, hp, hf, hL⟩
  · by_cases h7 : n = 7
    · subst h7
      exact Or.inr (Or.inl ⟨e⟩)
    · exact (F3 ((rankCertified_alternating (by omega)).of_mulEquiv e.symm)).elim
  · rcases hsp with h | h | h | h | h | h | h | h | h
    · exact Or.inr (Or.inr h)
    · exact (F3 (CFSG.GH74.E2.rank3_M12 h)).elim
    · exact (F3 (CFSG.GH74.E2.rank3_M22 h)).elim
    · exact (F3 (CFSG.GH74.E2.rank3_M23 h)).elim
    · exact (F2 (rankCertified_of_isSporadic_J1 h)).elim
    · exact (F3 (CFSG.GH74.E2.rank3_J2 h)).elim
    · exact (F3 (CFSG.GH74.E2.rank3_J3 h)).elim
    · exact (F3 (rankCertified_of_isSporadic_McL h)).elim
    · exact (F3 (rankCertified_of_isSporadic_Ly h)).elim
  · rcases hL with ⟨hp2, h | h | h | h | h | h⟩ | ⟨hp2, -, h⟩ | ⟨hp2, -, h⟩ | ⟨hq, h⟩ | ⟨hq, h⟩ | h |
        ⟨-, h | h | h | h | h⟩
    · exact Or.inl (Or.inl ⟨p, f, hp, hp2, hf, h⟩)
    · rcases three_lt_or_eq hp hp2 hf with ⟨rfl, rfl⟩ | h3
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr ⟨p, f, hp, hp2, h3, Or.inl h⟩))
    · rcases three_lt_or_eq hp hp2 hf with ⟨rfl, rfl⟩ | h3
      · exact (F2 (CFSG.GH74.E2.rank2_U3_3 h)).elim
      · exact Or.inl (Or.inr (Or.inr ⟨p, f, hp, hp2, h3, Or.inr h⟩))
    · obtain ⟨-, -, F, _, _, hFc, ⟨eS⟩⟩ := lieModel_psp_data h
      exact (F3 ((rankCertified_PSp4 (ringChar_ne_two_of_card_eq hp hp2 hFc)).of_mulEquiv
        eS.symm)).elim
    · exact (F3 (rankCertified_of_lieModel_G2 hp hp2 h)).elim
    · exact (F3 (rankCertified_of_lieModel_3D4 hp hp2 h)).elim
    · obtain ⟨-, -, F, _, _, hFc, ⟨eS⟩⟩ := lieModel_psl_data h
      exact (F3 ((rankCertified_PSL4 (ringChar_ne_two_of_card_eq hp hp2 hFc)).of_mulEquiv
        eS.symm)).elim
    · obtain ⟨-, -, F, _, _, hFc, ⟨eS⟩⟩ := lieModel_psu_data h
      exact (F3 ((rankCertified_PSU4 hFc (Nat.odd_iff.1 (odd_prime_pow hp hp2))).of_mulEquiv
        eS.symm)).elim
    · have hp2 : p ≠ 2 := prime_ne_two_of_pow_mod_four hf (Or.inr rfl) hq
      obtain ⟨-, -, F, _, _, hFc, ⟨eS⟩⟩ := lieModel_psl_data h
      exact (F3 ((rankCertified_PSL5 (ringChar_ne_two_of_card_eq hp hp2 hFc)).of_mulEquiv
        eS.symm)).elim
    · have hp2 : p ≠ 2 := prime_ne_two_of_pow_mod_four hf (Or.inl rfl) hq
      obtain ⟨-, -, F, _, _, hFc, ⟨eS⟩⟩ := lieModel_psu_data h
      exact (F3 ((rankCertified_PSU5 hFc (Nat.odd_iff.1 (odd_prime_pow hp hp2))).of_mulEquiv
        eS.symm)).elim
    · exact (F2 (B1.rankCertified_reeModel_two h)).elim
    · exact (F2 (CFSG.GH74.E2.rank2_L2_8 h)).elim
    · exact (F3 (CFSG.GH74.E2.rank3_L2_16 h)).elim
    · exact (F3 (CFSG.GH74.E2.rank3_L3_4 h)).elim
    · exact (F3 (CFSG.GH74.E2.rank3_U3_4 h)).elim
    · exact (F2 (CFSG.GH74.E2.rank2_Sz8 h)).elim

section Components

variable {G : Type} [Group G] [Finite G]

theorem le_centBarK_of_ne_barK {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1Core x K M Q H) (hc1 : barIn M H = barIn M K) {J : Subgroup (Mbar M)}
    (hJ : IsComponent J) (hJK : J ≠ barIn M K) : J ≤ SD.centBarK M K := by
  have hHsub : (barIn M H).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) h1.H_min.2.1.2
  have hKc : IsComponent (barIn M K) := isComponent_barIn_of_isSubnormal hs h1.K_le (hc1 ▸ hHsub)
  rcases CFSG.LocalCores.distinct_components_commute hJ hKc with h | h
  · exact absurd h hJK
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h

theorem ghList_quotient_center {x : G} {K A M P Q : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    {J : Subgroup (Mbar M)} (hq : IsQuasisimple ↥J) : GHList (↥J ⧸ center ↥J) := by
  let π : ↥M →* Mbar M := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let Kpre : Subgroup ↥M := J.comap π
  let H : Subgroup G := Kpre.map M.subtype
  have hHle : H ≤ M := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hH : H ≠ ⊤ := fun h => hs.maxM.1 (top_le_iff.1 (h ▸ hHle))
  let e₁ : ↥Kpre ≃* ↥H := Kpre.equivMapOfInjective M.subtype M.subtype_injective
  let q : ↥Kpre →* ↥J := (π.comp Kpre.subtype).codRestrict J fun k => k.2
  have hq' : Function.Surjective q := by
    intro k
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) (k : Mbar M)
    exact ⟨⟨c, show π c ∈ J by rw [hc]; exact k.2⟩, Subtype.ext hc⟩
  let f : ↥H →* ↥J ⧸ center ↥J :=
    ((QuotientGroup.mk' (center ↥J)).comp q).comp e₁.symm.toMonoidHom
  have hf : Function.Surjective f :=
    ((QuotientGroup.mk'_surjective _).comp hq').comp e₁.symm.surjective
  exact ghList_of_surjection hs.hyp.kgh hH f hf hq.2.1 hq.2.2

end Components

end SDSmallComp

section Statements

variable {G : Type} [Group G] [Finite G]

theorem smallComp_of_ne_barK
    {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1Core x K M Q H) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    (hc1 : barIn M H = barIn M K) {J : Subgroup (Mbar M)} (hJ : IsComponent J)
    (hJK : J ≠ barIn M K) : SmallComp ↥J :=
  SDSmallComp.smallComp_of_ghList
    (SD.sectionalRank_le_two_of_le_centBarK hs h1 h3
      (SDSmallComp.le_centBarK_of_ne_barK hs h1 hc1 hJ hJK))
    (SDSmallComp.ghList_quotient_center hs hJ.1)

end Statements

end CFSG.GH74.Generic.BProg.B2.SD2
