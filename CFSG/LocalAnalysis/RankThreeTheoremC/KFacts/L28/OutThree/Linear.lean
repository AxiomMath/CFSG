module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Reduction
public import CFSG.Open.StatedDefs
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedUnitary
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL5Proof
import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.Holt.Centralizer
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockCensus
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
import CFSG.RankThree.PartOne.N143.SectionCenter
import CFSG.RankThree.PartOne.N143.SectionRankBound
import CFSG.RankThree.PartOne.N143.SectionRankProof
import CFSG.RankThree.PartOne.N143.SectionRankSplit
import CFSG.RankThree.PartOne.N143.SectionReduce
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
import CFSG.Sporadic.Bridge.Fi24Data
import CFSG.Sporadic.Bridge.TableSurj
import CFSG.Sporadic.Fi24.Faithful
import CFSG.Sporadic.Fi24.SepSpec
import CFSG.Sporadic.Fi24.Simple
import CFSG.Sporadic.Presentation.Fi24PrimeExact
import CFSG.StronglyEmbedded.BenderNormalSeries
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate1016Base
import Certificates.Certificate19800
import Certificates.Certificate2
import Certificates.Certificate9207
import Certificates.Certificate9591
import Certificates.Certificate9594
import Certificates.Certificate9595
import Certificates.Certificate9597
import Certificates.Certificate9602

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  (autThreePowInner_of_not_three_dvd_outer)

variable {S : Type} [Group S]

theorem not_three_dvd_of_prime {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : ¬ 3 ∣ p := fun h =>
  hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm

theorem not_three_dvd_of_dvd_mul {f c n : ℕ} (hn : n ∣ f * c) (hf : ¬ 3 ∣ f) (hc : c ∣ 2) :
    ¬ 3 ∣ n := fun h3 => by
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans hn) with h | h
  · exact hf h
  · have := Nat.le_of_dvd (by norm_num) (h.trans hc)
    omega

theorem outCommInner_of_psl_two {p f : ℕ} (h : StatedClassicalModel S .PSL 2 p f) :
    OutCommInner S := by
  obtain ⟨-, F, _, _, -, ⟨e⟩⟩ := h
  exact OutCommInner.of_mulEquiv (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm)
    (outCommInner_of_outer_comm (OuterDerived.outer_psl2_mul_comm F))

theorem not_three_dvd_exponent_of_psl_two [Finite S] {p f : ℕ}
    (h : StatedClassicalModel S .PSL 2 p f) (hp3 : p ≠ 3)
    (h3 : (Nat.card S).factorization 3 = 1) : ¬ 3 ∣ f := by
  intro hf
  obtain ⟨⟨hp, -⟩, F, _, _, hF, ⟨e⟩⟩ := h
  have hcard : Nat.card (StatedProj (StatedSL 2 F)) =
      Nat.card F * (Nat.card F ^ 2 - 1) / Nat.gcd 2 (Nat.card F - 1) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), Finset.Icc_self,
      Finset.prod_singleton]
    norm_num
  rw [← Nat.card_congr e.toEquiv, hF] at hcard
  have hg : Nat.gcd 2 (p ^ f - 1) ∣ p ^ f * ((p ^ f) ^ 2 - 1) := by
    refine Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans ?_) _
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (p ^ f) 1 2
  have hmul : Nat.card S * Nat.gcd 2 (p ^ f - 1) = p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [hcard, Nat.div_mul_cancel hg]
  have h9 : 9 ∣ Nat.card S * Nat.gcd 2 (p ^ f - 1) :=
    hmul ▸ (nine_dvd_sq_sub_one (not_three_dvd_of_prime hp hp3) hf).mul_left _
  have hcop : Nat.Coprime 9 (Nat.gcd 2 (p ^ f - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 _) (by norm_num)
  exact not_nine_dvd_of_factorization h3 (hcop.dvd_of_dvd_mul_right h9)

theorem autThreePowInner_of_psl_two [Finite S] {p f : ℕ}
    (h : StatedClassicalModel S .PSL 2 p f) (hp3 : p ≠ 3)
    (h3 : (Nat.card S).factorization 3 = 1) : AutThreePowInner S := by
  have hf3 := not_three_dvd_exponent_of_psl_two h hp3 h3
  obtain ⟨⟨hp, -⟩, F, _, _, hF, ⟨e⟩⟩ := h
  have hout := (linear_two_outer_order_divisor hp F hF).2 S
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩
  exact autThreePowInner_of_not_three_dvd_outer
    (not_three_dvd_of_dvd_mul hout hf3 (Nat.gcd_dvd_left 2 _))

theorem gcd_three_sub_one {q : ℕ} (hq : q % 3 = 2) : Nat.gcd 3 (q - 1) = 1 :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)

theorem gcd_three_add_one {q : ℕ} (hq : q % 3 = 1) : Nat.gcd 3 (q + 1) = 1 :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)

theorem outCommInner_of_psl_three {p f : ℕ} (h : StatedClassicalModel S .PSL 3 p f)
    (hq : p ^ f % 3 = 2) : OutCommInner S := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  refine OutCommInner.of_mulEquiv
    ((e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)) ?_
  obtain ⟨N, -, hN, hcomm⟩ := OuterDerived.exists_linear_outer_diagonal (K := F) (n := 3) le_rfl
  rw [hF, gcd_three_sub_one hq, Nat.dvd_one] at hN
  exact outCommInner_of_outer_commutator_mem N hN hcomm

theorem not_three_dvd_exponent_of_psl_three [Finite S] {p f : ℕ}
    (h : StatedClassicalModel S .PSL 3 p f) (hq : p ^ f % 3 = 2)
    (h3 : (Nat.card S).factorization 3 = 1) : ¬ 3 ∣ f := by
  intro hf
  obtain ⟨⟨-, hf1, -⟩, F, _, _, hF, ⟨e⟩⟩ := h
  have hmul := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := F)
  rw [← Nat.card_congr e.toEquiv, hF, gcd_three_sub_one hq, mul_one] at hmul
  have hp3 : ¬ 3 ∣ p := fun h3p => by
    have : 3 ∣ p ^ f := dvd_pow h3p (by omega)
    omega
  have h9 : 9 ∣ Nat.card S :=
    hmul ▸ ((nine_dvd_sq_sub_one hp3 hf).mul_left _).mul_right _
  exact not_nine_dvd_of_factorization h3 h9

theorem autThreePowInner_of_psl_three [Finite S] {p f : ℕ}
    (h : StatedClassicalModel S .PSL 3 p f) (hq : p ^ f % 3 = 2)
    (h3 : (Nat.card S).factorization 3 = 1) : AutThreePowInner S := by
  have hf3 := not_three_dvd_exponent_of_psl_three h hq h3
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inl rfl) le_rfl h.1.1 h.1.2.1 h).1
  rw [CFSG.RankThree.OuterOrder.determinantParameter, gcd_three_sub_one hq, mul_one,
    mul_comm] at hout
  exact autThreePowInner_of_not_three_dvd_outer
    (not_three_dvd_of_dvd_mul hout hf3 dvd_rfl)

theorem outCommInner_of_psu_three {p f : ℕ} (h : StatedClassicalModel S .PSU 3 p f)
    (hq : p ^ f % 3 = 1) : OutCommInner S := by
  obtain ⟨⟨hp, hf, -⟩, F, _, _, hF, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hq2 : ¬(3 = 3 ∧ p ^ f = 2) := fun h2 => by omega
  obtain ⟨⟨eP⟩, -⟩ := UnitaryHigher.unitary_full_diagonal_outer_order hU (n := 3) le_rfl hq2
  refine OutCommInner.of_mulEquiv
    ((e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by norm_num)).symm).trans
      eP.symm) ?_
  obtain ⟨N, -, hN, hcomm⟩ := OuterDerived.exists_unitary_outer_diagonal hU (n := 3) le_rfl hq2
  rw [gcd_three_add_one hq, Nat.dvd_one] at hN
  exact outCommInner_of_outer_commutator_mem N hN hcomm

theorem not_three_dvd_exponent_of_psu_three [Finite S] {p f : ℕ}
    (h : StatedClassicalModel S .PSU 3 p f) (hq : p ^ f % 3 = 1)
    (h3 : (Nat.card S).factorization 3 = 1) : ¬ 3 ∣ f := by
  intro hf3
  obtain ⟨⟨hp, hf, -⟩, F, _, _, hF, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hmul := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul hU
  rw [← Nat.card_congr e.toEquiv, gcd_three_add_one hq, mul_one] at hmul
  have hp3 : ¬ 3 ∣ p := fun h3p => by
    have : 3 ∣ p ^ f := dvd_pow h3p (by omega)
    omega
  have h9 : 9 ∣ Nat.card S :=
    hmul ▸ ((nine_dvd_sq_sub_one hp3 hf3).mul_left _).mul_right _
  exact not_nine_dvd_of_factorization h3 h9

theorem autThreePowInner_of_psu_three [Finite S] {p f : ℕ}
    (h : StatedClassicalModel S .PSU 3 p f) (hq : p ^ f % 3 = 1)
    (h3 : (Nat.card S).factorization 3 = 1) : AutThreePowInner S := by
  have hf3 := not_three_dvd_exponent_of_psu_three h hq h3
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inr rfl) le_rfl h.1.1 h.1.2.1 h).1
  rw [CFSG.RankThree.OuterOrder.determinantParameter, gcd_three_add_one hq, mul_one,
    mul_comm] at hout
  exact autThreePowInner_of_not_three_dvd_outer
    (not_three_dvd_of_dvd_mul hout hf3 dvd_rfl)

end CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree
