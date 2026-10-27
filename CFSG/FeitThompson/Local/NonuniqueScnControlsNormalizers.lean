module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Definitions.LocalComplementaryPrimeConstraint
import CFSG.FeitThompson.Local.NonuniqueScnAuxiliaryPrime
import CFSG.FeitThompson.Local.ThompsonTransitivityRankThreeScn
import CFSG.FeitThompson.Local.SubnormalConstrainedTransitivity
import CFSG.FeitThompson.Local.AbelianSylowRankTwoLocalConstraint
import CFSG.FeitThompson.Local.PrimeExtensionMaximalInvariantSubgroup
import CFSG.FeitThompson.Local.SelfCentralizingAbelianSylowConstraint
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] {p : ℕ}

theorem subgroupPrimeSupport_eq_singleton_of_isPGroup [Finite G] (hp : p.Prime) {A : Subgroup G}
    (hA : IsPGroup p ↥A) (hAbot : A ≠ ⊥) : subgroupPrimeSupport A = {p} := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hAbot (Subgroup.card_eq_one.1 (by simpa using hn))
  rw [subgroupPrimeSupport_def, hn, Nat.primeFactors_pow _ hn0, hp.primeFactors]
  simp

theorem normalizer_le_of_le_inf_of_scn [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hp : p.Prime) (P : Sylow p G) {A M R : Subgroup G}
    (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A)
    (hAtwo : ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ A ≤ M₁ ∧ A ≤ M₂ ∧ M₁ ≠ M₂)
    (hM : IsCoatom M) (hCM : centralizer (A : Set G) ≤ M)
    (hAR : A ≤ R) (hRPM : R ≤ (P : Subgroup G) ⊓ M) :
    normalizer (R : Set G) ≤ M := by
  have := Fact.mk hp
  have hAP : A ≤ (P : Subgroup G) := hAself ▸ inf_le_right
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_inf_centralizer_eq hAself
  have hA3 : 3 ∈ elementaryAbelianRanks p ↥A := (le_elementaryAbelianPRank_iff hp.one_lt).1 hArank
  have hA2 : 2 ∈ elementaryAbelianRanks p ↥A := mem_elementaryAbelianRanks_of_le (by omega) hA3
  have hAne : A ≠ ⊥ := ne_bot_of_two_mem_elementaryAbelianRanks hp hA2
  have hApg : IsPGroup p ↥A := P.isPGroup'.to_le hAP
  have hπ : subgroupPrimeSupport A = {p} :=
    subgroupPrimeSupport_eq_singleton_of_isPGroup hp hApg hAne
  have hcon : IsConstrained A :=
    isConstrained_of_normal_selfCentralizing_sylow hna hodd hsolv hp P hAnormal hAself hA2
  obtain ⟨q, hq, hqp, J, hJM, hJnormal, hJpg, hJne, hJctrl⟩ :=
    exists_prime_ne_normal_isPGroup_forall_normalizer_le_of_scn hna hodd hsolv hp
      (P := (P : Subgroup G)) P.card_eq_multiplicity hAP hAnormal hAcomm
      (by rw [inf_comm]; exact hAself) hArank hAtwo hM hCM
  have hconj : ∀ Q₁ ∈ maximalNormalizedPSubgroups A q, ∀ Q₂ ∈ maximalNormalizedPSubgroups A q,
      ∃ k ∈ constrainedCentralizerCore A, (MulAut.conj k⁻¹ • Q₁ : Subgroup G) = Q₂ := by
    intro Q₁ hQ₁ Q₂ hQ₂
    rw [constrainedCentralizerCore_eq_pComplCoreIn_centralizer hp hApg hAne]
    exact exists_mem_pComplCoreIn_centralizer_conj_inv_smul_eq_of_rank_three_sylow hna hodd hsolv
      hp P hAnormal hAself hA3 hq hqp hQ₁ hQ₂
  have hRP : R ≤ (P : Subgroup G) := hRPM.trans inf_le_left
  have hRM : R ≤ M := hRPM.trans inf_le_right
  have hRpg : IsPGroup p ↥R := P.isPGroup'.to_le hRP
  have hPnormA : (P : Subgroup G) ≤ normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).1 hAnormal
  have hARnormal : (A.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAR).2 (hRP.trans hPnormA)
  have hRtop : R < ⊤ := lt_of_le_of_lt hRM (lt_top_iff_ne_top.2 hM.1)
  have hRπ : IsPiSubgroup (subgroupPrimeSupport A) R := by
    rw [hπ]; exact (isPiSubgroup_singleton_iff hp R).2 hRpg
  have hqπ : q ∉ subgroupPrimeSupport A := by rw [hπ]; simpa using hqp
  have hRJ : R ≤ normalizer (J : Set G) :=
    hRM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJM).1 hJnormal)
  obtain ⟨Q, hQ, hJQ⟩ := exists_mem_maximalNormalizedPSubgroups_ge (A := R) hJpg hRJ
  have htrans := exists_mem_constrainedCentralizerCore_conj_smul_eq_of_isSubnormal hna hsolv
    (bot_lt_iff_ne_bot.2 hAne) hcon hq hqπ hAR hRtop hRπ hARnormal.isSubnormal hconj
  intro x hx
  have hxR : (MulAut.conj x⁻¹ • R : Subgroup G) = R :=
    conj_smul_eq_self_iff_mem_normalizer.2 (inv_mem hx)
  obtain ⟨c, hc, hceq⟩ := htrans Q hQ _ (smul_mem_maximalNormalizedPSubgroups hxR hQ)
  have hcM : c ∈ M :=
    hCM (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hAR)
      (constrainedCentralizerCore_le_centralizer R hc))
  have h1 : (MulAut.conj (x * c⁻¹) • Q : Subgroup G) = Q := by
    rw [map_mul, mul_smul, hceq, map_inv, smul_inv_smul]
  have h2 : x * c⁻¹ ∈ M :=
    hJctrl Q (isPGroup_of_mem hQ) hJQ (conj_smul_eq_self_iff_mem_normalizer.1 h1)
  simpa using mul_mem h2 hcM

theorem sylow_le_of_scn [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hp : p.Prime) (P : Sylow p G) {A M : Subgroup G}
    (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A)
    (hAtwo : ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ A ≤ M₁ ∧ A ≤ M₂ ∧ M₁ ≠ M₂)
    (hM : IsCoatom M) (hCM : centralizer (A : Set G) ≤ M) :
    (P : Subgroup G) ≤ M := by
  have hAP : A ≤ (P : Subgroup G) := hAself ▸ inf_le_right
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_inf_centralizer_eq hAself
  have hAM : A ≤ M := (Subgroup.le_centralizer A).trans hCM
  have hPnormA : (P : Subgroup G) ≤ normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).1 hAnormal
  exact hPnormA.trans (normalizer_le_of_le_inf_of_scn hna hodd hsolv hp P hAnormal hAself hArank
    hAtwo hM hCM le_rfl (le_inf hAP hAM))

theorem normalizer_sylow_le_of_scn [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hp : p.Prime) (P : Sylow p G) {A M : Subgroup G}
    (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A)
    (hAtwo : ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ A ≤ M₁ ∧ A ≤ M₂ ∧ M₁ ≠ M₂)
    (hM : IsCoatom M) (hCM : centralizer (A : Set G) ≤ M) :
    normalizer ((P : Subgroup G) : Set G) ≤ M :=
  normalizer_le_of_le_inf_of_scn hna hodd hsolv hp P hAnormal hAself hArank hAtwo hM hCM
    (hAself ▸ inf_le_right)
    (le_inf le_rfl (sylow_le_of_scn hna hodd hsolv hp P hAnormal hAself hArank hAtwo hM hCM))

end

end CFSG.FeitThompson
