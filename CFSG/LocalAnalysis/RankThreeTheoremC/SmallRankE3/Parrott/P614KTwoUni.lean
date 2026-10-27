module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614KTwoBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.Open.Catalog
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614KTwo

open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem mem_of_pow_two_pow_eq_one {G : Type*} [Group G] {I D : Subgroup G} [I.Normal]
    (hodd : Odd (Nat.card (D ⧸ I.subgroupOf D))) {α : G} (hα : α ∈ D) {k : ℕ}
    (hk : α ^ 2 ^ k = 1) : α ∈ I := by
  have ha : (⟨α, hα⟩ : D) ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk)
  have h1 : ((⟨α, hα⟩ : D) : D ⧸ I.subgroupOf D) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, ha, QuotientGroup.mk_one]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have h3 := orderOf_dvd_natCard ((⟨α, hα⟩ : D) : D ⧸ I.subgroupOf D)
  have h4 : orderOf ((⟨α, hα⟩ : D) : D ⧸ I.subgroupOf D) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)) h2 h3
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h4
  exact h4

theorem outTwoCyclic_primeFormP {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : ¬(3 = 3 ∧ p ^ f = 2)) :
    OutTwoCyclic (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  have : Finite K := h.finite
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_one (n := 3) (K := K))
      le_rfl hq
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h (n := 3) le_rfl hq
  haveI := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  refine ⟨K ≃+* K, inferInstance, inferInstance,
    primeFormFieldFactor h isPrimeFormGram_one le_rfl hq, fun α hα ⟨k, hk⟩ => ?_⟩
  rw [hFker] at hα
  refine mem_of_pow_two_pow_eq_one (I := inner _) ?_ hα hk
  rw [hcard]
  exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)

theorem outTwoCyclic_psu3 {f : ℕ} (hf : 2 ≤ f) : OutTwoCyclic (CFSG.Open.PSU3 2 f) := by
  have h1 : 1 ≤ f := by omega
  have hq : ¬(3 = 3 ∧ 2 ^ f = 2) := fun ⟨_, h2⟩ => by
    have : 2 ^ 1 < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hU := CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.unitaryFieldData_galoisField h1
  obtain ⟨⟨eT⟩, -⟩ := unitary_full_diagonal_outer_order hU (n := 3) le_rfl hq
  exact OutTwoCyclic.of_mulEquiv
    (((CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative f).symm.trans
      (unitaryPSUEquiv hU (by norm_num)).symm).trans eT.symm)
    (outTwoCyclic_primeFormP hU hq)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614KTwo
