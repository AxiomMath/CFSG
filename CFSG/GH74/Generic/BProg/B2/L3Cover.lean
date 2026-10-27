module

public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.GH74.Generic.BProg.B2.L2Cover
public import CFSG.GH74.Generic.BProg.B2.FamilyOddCentre
public import CFSG.GH74.Generic.BProg.B2.FamilyGeneric
public import CFSG.GH74.Generic.JMaxCongr
public import CFSG.Certificates.Kernel.Spor.ONKSound
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
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.Generic.BProg.B1.Assembly2
public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
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
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover Subgroup
open scoped MatrixGroups

namespace L3Cover

theorem odd_gcd_three (m : ℕ) : Odd (Nat.gcd 3 m) :=
  Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 m)

theorem center_eq_bot_or_odd_of {J X : Type} [Group J] [Finite J] [Group X] (hq : IsQuasisimple J)
    (e : J ⧸ center J ≃* X) (hodd : Odd (Nat.card (hopfMultiplier X))) :
    (∃ z : J, z ≠ 1 ∧ (∀ g : J, g * z = z * g) ∧ Odd (orderOf z)) ∨ center J = ⊥ := by
  by_cases hz : ∃ z : J, z ≠ 1 ∧ (∀ g : J, g * z = z * g) ∧ Odd (orderOf z)
  · exact Or.inl hz
  right
  have h2 := L2Cover.isPGroup_two_center_of_no_odd hz
  have hdvd := L2Cover.card_center_dvd_card_hopfMultiplier_qs hq e
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hk0 : k = 0 := by
    by_contra hne
    have h2d : 2 ∣ Nat.card (center J) := hk ▸ dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2d.trans hdvd))
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem card_hopf_psl3 {k : Type} [Field k] [Fintype k] (hk : 3 ≤ Fintype.card k)
    (h34 : Fintype.card k ≠ 4) :
    Nat.card (hopfMultiplier PSL(3, k)) = Nat.gcd 3 (Fintype.card k - 1) := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_three_le
    (n := 3) le_rfl hk (fun h => h34 h.2)
  rw [← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem odd_card_hopf_psl3 {k : Type} [Field k] [Fintype k] (hk : 3 ≤ Fintype.card k)
    (h34 : Fintype.card k ≠ 4) : Odd (Nat.card (hopfMultiplier PSL(3, k))) := by
  rw [card_hopf_psl3 hk h34]
  exact odd_gcd_three _

theorem odd_card_hopf_psu3
    {p f : ℕ} (hp : p.Prime) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (p ^ f) ^ 2) (hf : 1 ≤ f) (hne : (3, p ^ f) ≠ (3, 2)) :
    Odd (Nat.card (hopfMultiplier (StatedProj (StatedSU 3 (p ^ f) F)))) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow hp hF
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier hF hf
    (by norm_num) (by decide) hne
  rw [← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact odd_gcd_three _

end L3Cover

theorem l3_cover_cases
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (h : QShape3 (J ⧸ center J)) :
    (∃ z : J, z ≠ 1 ∧ (∀ g : J, g * z = z * g) ∧ Odd (orderOf z)) ∨
      (center J = ⊥ ∧ QShape3 J) := by
  have hdich : (∃ z : J, z ≠ 1 ∧ (∀ g : J, g * z = z * g) ∧ Odd (orderOf z)) ∨ center J = ⊥ := by
    obtain ⟨p, f, hp, hp2, h3, hL | hU⟩ := h
    · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel
        hL (by decide)
      have : Fintype K := Fintype.ofFinite K
      have hcard : Fintype.card K = p ^ f := Fintype.card_eq_nat_card.trans hK
      have hoddq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
      refine L3Cover.center_eq_bot_or_odd_of hq
        (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm) ?_
      refine L3Cover.odd_card_hopf_psl3 (by omega) ?_
      intro h4
      rw [hcard] at h4
      rw [h4] at hoddq
      exact absurd hoddq (by decide)
    · obtain ⟨⟨hp', hf, -, hne⟩, K, _, _, hK, ⟨e⟩⟩ :=
        CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel hU (by decide)
      exact L3Cover.center_eq_bot_or_odd_of hq e
        (L3Cover.odd_card_hopf_psu3 hp hK hf hne)
  rcases hdich with hz | hc
  · exact Or.inl hz
  · refine Or.inr ⟨hc, ?_⟩
    have e : J ⧸ center J ≃* J := (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    exact isL3OddGt3_of_mulEquiv e h

theorem l3_three_cover_center {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (h : LieModel (J ⧸ center J) .PSL 3 3 1) : center J = ⊥ ∧ LieModel J .PSL 3 3 1 := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel
    h (by decide)
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := (Fintype.card_eq_nat_card.trans hK).trans (by norm_num)
  have e' := e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
  have hdvd := L2Cover.card_center_dvd_card_hopfMultiplier_qs hq e'
  rw [L3Cover.card_hopf_psl3 (by omega) (by omega), hcard] at hdvd
  have h1 : Nat.card (center J) = 1 := by
    have : Nat.gcd 3 (3 - 1) = 1 := by decide
    rw [this] at hdvd
    exact Nat.dvd_one.1 hdvd
  have hc : center J = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  refine ⟨hc, ?_⟩
  have e2 : J ≃* J ⧸ center J :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm))
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e2.symm h

theorem weakSig2NormG4_of_qShape3Cover
    (hs3 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → QShape3 J → WeakSig2NormG4 J)
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) (h : QShape3 (J ⧸ center J)) :
    WeakSig2NormG4 J := by
  rcases l3_cover_cases hq h with hz | ⟨-, h3⟩
  · exact weakSig2NormG4_of_odd_central hz
  · exact hs3 J hq h3

theorem weakSig2NormG4_of_l3Three
    (hg : ∀ (J : Type) [Group J] [Finite J], LieModel J .PSL 3 3 1 → GenLoc4 J)
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (h : LieModel (J ⧸ center J) .PSL 3 3 1) : WeakSig2NormG4 J := by
  obtain ⟨-, hJ⟩ := l3_three_cover_center hq h
  exact FamilyGeneric.weakSig2NormG4_of_genLoc4_qs hq (hg J hJ)

end CFSG.GH74.Generic.BProg.B2
