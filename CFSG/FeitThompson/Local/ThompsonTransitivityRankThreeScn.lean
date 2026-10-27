module

public import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
public import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
public import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
import CFSG.FeitThompson.Local.AbelianSylowRankTwoLocalConstraint
import CFSG.FeitThompson.Local.CentralRankThreeConstrainedTransitivity
import CFSG.FeitThompson.Local.SelfCentralizingAbelianSylowConstraint
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
import CFSG.FeitThompson.Local.ConjugationUniqueMaximalOvergroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {p q : ℕ}

theorem constrainedCentralizerCore_eq_pComplCoreIn_centralizer [Finite G] (hp : p.Prime)
    {A : Subgroup G} (hA : IsPGroup p ↥A) (hAbot : A ≠ ⊥) :
    constrainedCentralizerCore A = pComplCoreIn p (centralizer (A : Set G)) := by
  rw [constrainedCentralizerCore_eq, subgroupPrimeSupportCompl_eq_of_isPGroup hp hA hAbot,
    map_piCore_setOf_prime_ne_eq_pComplCoreIn]

theorem exists_mem_pComplCoreIn_centralizer_conj_inv_smul_eq_of_rank_three_sylow [Finite G]
    [IsSimpleGroup G] (hGnc : ¬ IsMulCommutative G) (hGodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) (hp : p.Prime) (P : Sylow p G)
    {A : Subgroup G} (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A)
    (hA : 3 ∈ elementaryAbelianRanks p ↥A) (hq : q.Prime) (hqp : q ≠ p)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ maximalNormalizedPSubgroups A q)
    (hQ₂ : Q₂ ∈ maximalNormalizedPSubgroups A q) :
    ∃ k ∈ pComplCoreIn p (centralizer (A : Set G)), MulAut.conj k⁻¹ • Q₁ = Q₂ := by
  have hAP : A ≤ (P : Subgroup G) := hAself ▸ inf_le_right
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_inf_centralizer_eq hAself
  have hA2 : 2 ∈ elementaryAbelianRanks p ↥A :=
    mem_elementaryAbelianRanks_of_le (Nat.le_succ 2) hA
  have hAne : A ≠ ⊥ := ne_bot_of_two_mem_elementaryAbelianRanks hp hA2
  have hAbot : ⊥ < A := bot_lt_iff_ne_bot.2 hAne
  have hAtop : A < ⊤ := lt_top_of_normal_selfCentralizing_sylow hGnc hp P hAP hA2
  have hcon : IsConstrained A :=
    isConstrained_of_normal_selfCentralizing_sylow hGnc hGodd hsolv hp P hAnormal hAself hA2
  have hApg : IsPGroup p ↥A := P.isPGroup'.to_le hAP
  have hpi : subgroupPrimeSupportCompl A = {r : ℕ | r.Prime ∧ r ≠ p} :=
    subgroupPrimeSupportCompl_eq_of_isPGroup hp hApg hAne
  have hqπ : q ∉ subgroupPrimeSupport A :=
    (mem_subgroupPrimeSupportCompl_iff.1 (hpi ▸ (⟨hq, hqp⟩ : q ∈ {r : ℕ | r.Prime ∧ r ≠ p}))).2
  obtain ⟨E, hEA, -, hEexp, hEcard⟩ := (mem_elementaryAbelianRanks_subgroup_iff hp).1 hA
  obtain ⟨e⟩ := nonempty_mulEquiv_pi_of_le_of_card hp hEA hEexp hEcard
  have hE : Nonempty (↥E ≃* Multiplicative (Fin 3 → ZMod p)) :=
    ⟨e.trans (MulEquiv.piMultiplicative _).symm⟩
  have hEZ : E ≤ A ⊓ centralizer (A : Set G) :=
    le_inf hEA (hEA.trans (Subgroup.le_centralizer_iff_isMulCommutative.2 hAcomm))
  rw [← constrainedCentralizerCore_eq_pComplCoreIn_centralizer hp hApg hAne]
  exact exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_rank_three_le_centre hsolv
    hAbot hAtop hcon hq hqπ hp hEZ hE hQ₁ hQ₂

theorem exists_mem_pComplCoreIn_centralizer_forall_mem_iff_of_rank_three_sylow [Finite G]
    [IsSimpleGroup G] (hGnc : ¬ IsMulCommutative G) (hGodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) (hp : p.Prime) (P : Sylow p G)
    {A : Subgroup G} (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A)
    (hA : 3 ∈ elementaryAbelianRanks p ↥A) (hq : q.Prime) (hqp : q ≠ p)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ maximalNormalizedPSubgroups A q)
    (hQ₂ : Q₂ ∈ maximalNormalizedPSubgroups A q) :
    ∃ k ∈ pComplCoreIn p (centralizer (A : Set G)), ∀ x : G, x ∈ Q₂ ↔ k * x * k⁻¹ ∈ Q₁ := by
  obtain ⟨k, hk, hkeq⟩ := exists_mem_pComplCoreIn_centralizer_conj_inv_smul_eq_of_rank_three_sylow
    hGnc hGodd hsolv hp P hAnormal hAself hA hq hqp hQ₁ hQ₂
  exact ⟨k, hk, fun x => by rw [← hkeq, mem_conj_inv_smul_iff]⟩

end

end CFSG.FeitThompson

