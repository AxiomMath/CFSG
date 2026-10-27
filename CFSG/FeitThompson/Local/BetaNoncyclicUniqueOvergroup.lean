module

public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.PlaneRankThreeCentralizerUniqueness
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.MetacyclicOddGroupUniqueTorsionPlane
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} {R : Subgroup G}

theorem ne_bot_of_not_isCyclic (hnc : ¬ IsCyclic ↥R) : R ≠ ⊥ := by
  rintro rfl
  exact hnc isCyclic_of_subsingleton

theorem lt_top_of_not_isCyclic_of_mem_betaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hp : p ∈ betaPrimes G) (hRp : IsPGroup p ↥R)
    (hnc : ¬ IsCyclic ↥R) : R < ⊤ :=
  lt_top_of_isPGroup hna (prime_of_mem_betaPrimes hp) (ne_bot_of_not_isCyclic hnc) hRp

theorem exists_isUniqueMaximalOvergroup_of_not_isCyclic_of_mem_betaPrimes [Finite G]
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X) (hp : p ∈ betaPrimes G)
    (hRp : IsPGroup p ↥R) (hnc : ¬ IsCyclic ↥R) :
    ∃ M : Subgroup G, IsUniqueMaximalOvergroup R M := by
  have hpp : p.Prime := prime_of_mem_betaPrimes hp
  have := Fact.mk hpp
  have hoddp : Odd p := hodd.of_dvd_nat (dvd_card_of_mem_betaPrimes hp)
  obtain ⟨E, hEcard, hEexp⟩ := exists_natCard_eq_prime_sq_forall_pow_eq_one hpp hoddp hRp hnc
  set A : Subgroup G := E.map R.subtype with hAdef
  have hAR : A ≤ R := Subgroup.map_subtype_le E
  have hAcard : Nat.card ↥A = p ^ 2 := by
    rw [hAdef, Subgroup.card_map_of_injective R.subtype_injective, hEcard]
  have hAexp : ∀ x ∈ A, x ^ p = 1 := by
    rintro x ⟨e, he, rfl⟩
    rw [← map_pow, hEexp e he, map_one]
  have hAea : IsElementaryAbelian p A :=
    isElementaryAbelian_iff.2
      ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hAcard, hAexp⟩
  obtain ⟨P, hRP⟩ := hRp.exists_le_sylow
  have hAP : A ≤ (P : Subgroup G) := hAR.trans hRP
  have hnarrow := not_isPNarrow_of_mem_betaPrimes hp P
  have hAsub : IsElementaryAbelianSubgroup p (A.subgroupOf (P : Subgroup G)) :=
    (isElementaryAbelian_iff_isElementaryAbelianSubgroup.1 hAea).comap
      (P : Subgroup G).subtype_injective
  have hAsubcard : Nat.card ↥(A.subgroupOf (P : Subgroup G)) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hAcard]
  obtain ⟨B, hAB, hBmax⟩ := exists_maximal_isElementaryAbelianSubgroup_ge hAsub
  have hBne : B ≠ A.subgroupOf (P : Subgroup G) := fun h =>
    hnarrow (isPNarrow_of_maximal_card_eq (h ▸ hBmax) hAsubcard)
  have hcardlt : Nat.card ↥(A.subgroupOf (P : Subgroup G)) < Nat.card ↥B := by
    by_contra h
    exact hBne (Subgroup.eq_of_le_of_card_ge hAB (not_lt.1 h)).symm
  obtain ⟨d, hd⟩ := hBmax.prop.isPGroup.exists_card_eq
  have hd3 : 3 ≤ d := by
    rw [hAsubcard, hd] at hcardlt
    have := (Nat.pow_lt_pow_iff_right hpp.one_lt).1 hcardlt
    omega
  have hB'ea : IsElementaryAbelianSubgroup p (B.map (P : Subgroup G).subtype) := hBmax.prop.map _
  have hB'card : Nat.card ↥(B.map (P : Subgroup G).subtype) = p ^ d := by
    rw [Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective, hd]
  have hAB' : A ≤ B.map (P : Subgroup G).subtype := fun x hx =>
    ⟨⟨x, hAP hx⟩, hAB (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hB'cent : B.map (P : Subgroup G).subtype ≤ centralizer (A : Set G) := fun b hb =>
    mem_centralizer_iff.2 fun a ha => hB'ea.mul_comm a (hAB' ha) b hb
  have hrank : 3 ≤ elementaryAbelianPRank p ↥(centralizer (A : Set G)) :=
    le_trans hd3 ((isElementaryAbelian_iff_isElementaryAbelianSubgroup.2
      hB'ea).le_elementaryAbelianPRank hpp hB'card hB'cent)
  obtain ⟨M, hM⟩ :=
    exists_isUniqueMaximalOvergroup_of_plane_of_three_le_elementaryAbelianPRank_centralizer
      hpp hpp hna hodd hsolv hAea hAcard hrank
  exact ⟨M, hM.mono hAR (lt_top_of_not_isCyclic_of_mem_betaPrimes hna hp hRp hnc).ne⟩

theorem existsUnique_isCoatom_ge_of_not_isCyclic_of_mem_betaPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X) (hp : p ∈ betaPrimes G)
    (hRp : IsPGroup p ↥R) (hnc : ¬ IsCyclic ↥R) : ∃! M : Subgroup G, IsCoatom M ∧ R ≤ M := by
  obtain ⟨M, hM⟩ := exists_isUniqueMaximalOvergroup_of_not_isCyclic_of_mem_betaPrimes
    hna hodd hsolv hp hRp hnc
  exact ⟨M, ⟨hM.isCoatom, hM.le⟩, fun N hN => hM.eq_of_isCoatom hN.1 hN.2⟩

end

end CFSG.FeitThompson
