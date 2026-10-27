module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Local.PLengthOneSubgroupInheritance
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p : ℕ} {X : Type*} [Group X]

theorem isCyclic_or_maximal_plane_of_isPNarrow {P : Type*} [Group P] [Finite P] (hp : p.Prime)
    (hodd : Odd p) (hPp : IsPGroup p P) (h : IsPNarrow p P) :
    IsCyclic P ∨ ∃ A : Subgroup P, Maximal (IsElementaryAbelian p) A ∧ Nat.card A = p ^ 2 := by
  have := Fact.mk hp
  rw [isPNarrow_iff] at h
  rcases h with hrank | ⟨A, hA, hAcard⟩
  · by_cases hcyc : IsCyclic P
    · exact Or.inl hcyc
    refine Or.inr ?_
    have hnc : ¬ IsCyclic ↥(⊤ : Subgroup P) := fun _ =>
      hcyc (isCyclic_of_surjective (⊤ : Subgroup P).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩)
    obtain ⟨E, -, -, hE⟩ :=
      exists_normal_le_mulEquiv_pi_of_not_isCyclic hp hodd hPp (⊤ : Subgroup P) hnc
    have hEea : IsElementaryAbelianSubgroup p E :=
      isElementaryAbelian_iff_isElementaryAbelianSubgroup.1
        (isElementaryAbelian_of_nonempty_mulEquiv_pi hE)
    have hEcard : Nat.card E = p ^ 2 := by
      obtain ⟨f⟩ := hE
      rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]
    obtain ⟨B, hEB, hB⟩ := exists_maximal_isElementaryAbelianSubgroup_ge hEea
    obtain ⟨d, hd⟩ := hB.prop.isPGroup.exists_card_eq
    have hd2 : d ≤ 2 :=
      le_trans (le_elementaryAbelianPRank hp.one_lt
        (hB.prop.mem_elementaryAbelianRanks hp hd)) hrank
    have h2d : 2 ≤ d := by
      have hdvd : p ^ 2 ∣ p ^ d := by
        rw [← hEcard, ← hd]; exact Subgroup.card_dvd_of_le hEB
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
    exact ⟨B, (maximal_congr fun _ => isElementaryAbelian_iff_isElementaryAbelianSubgroup).2 hB,
      by rw [hd, Nat.le_antisymm hd2 h2d]⟩
  · exact Or.inr ⟨A, (maximal_congr fun _ =>
      isElementaryAbelian_iff_isElementaryAbelianSubgroup).2 hA, hAcard⟩

variable [Finite X]

theorem isNormalPComplement_pComplCore_commutator_of_card [Group.IsSolvable X] {P : Subgroup X}
    (hp : p.Prime) (hodd : Odd p) (hoddX : Odd (Nat.card X))
    (hP : Nat.card P = p ^ (Nat.card X).factorization p) (hnarrow : IsPNarrow p ↥P)
    (hlen : HasPLengthLeOne p X) :
    IsNormalPComplement p (pComplCore p ↥(commutator X)) := by
  have := Fact.mk hp
  refine isNormalPComplement_of (by rw [pComplCore_eq_piCore]; exact piCore_normal _ _)
    (not_dvd_natCard_pComplCore hp _) ?_
  by_cases hpX : p ∣ Nat.card X
  ·
    have halt := isCyclic_or_maximal_plane_of_isPNarrow hp hodd (IsPGroup.of_card hP) hnarrow
    have hV : ¬ p ∣ (pComplPCore p X).index :=
      hasPLengthLeOne_iff_not_dvd_index_pComplPCore.1 hlen
    have h := isNormalPComplement_inf_commutator (P := P) hp hoddX hpX hP hV halt
    rw [← h.eq_pComplCore hp]
    exact h.exists_index_eq_pow
  ·
    have hcard : ¬ p ∣ Nat.card ↥(commutator X) := fun hd =>
      hpX (hd.trans (Subgroup.card_subgroup_dvd_card _))
    have htop : pComplCore p ↥(commutator X) = ⊤ := by
      refine top_le_iff.1 (le_pComplCore (Subgroup.normal_of_characteristic ⊤) ?_)
      intro hmem
      rw [Subgroup.card_top] at hmem
      exact hcard (Nat.dvd_of_mem_primeFactors hmem)
    exact ⟨0, by rw [htop, Subgroup.index_top, pow_zero]⟩

theorem isNormalPComplement_pComplCore_commutator [Group.IsSolvable X] (hp : p.Prime)
    (hodd : Odd p) (hoddX : Odd (Nat.card X)) (P : Sylow p X)
    (hnarrow : IsPNarrow p ↥(P : Subgroup X))
    (hlen : HasPLengthLeOne p X) :
    IsNormalPComplement p (pComplCore p ↥(commutator X)) :=
  have := Fact.mk hp
  isNormalPComplement_pComplCore_commutator_of_card hp hodd hoddX P.card_eq_multiplicity hnarrow
    hlen

theorem not_dvd_natCard_pComplCore_commutator [Group.IsSolvable X] (hp : p.Prime) (hodd : Odd p)
    (hoddX : Odd (Nat.card X)) (P : Sylow p X) (hnarrow : IsPNarrow p ↥(P : Subgroup X))
    (hlen : HasPLengthLeOne p X) : ¬ p ∣ Nat.card ↥(pComplCore p ↥(commutator X)) :=
  (isNormalPComplement_pComplCore_commutator hp hodd hoddX P hnarrow hlen).not_dvd_natCard

theorem exists_index_pComplCore_commutator_eq_pow [Group.IsSolvable X] (hp : p.Prime)
    (hodd : Odd p) (hoddX : Odd (Nat.card X)) (P : Sylow p X)
    (hnarrow : IsPNarrow p ↥(P : Subgroup X)) (hlen : HasPLengthLeOne p X) :
    ∃ n : ℕ, (pComplCore p ↥(commutator X)).index = p ^ n :=
  (isNormalPComplement_pComplCore_commutator hp hodd hoddX P hnarrow hlen).exists_index_eq_pow

theorem pComplCore_commutator_eq_inf_subgroupOf [Group.IsSolvable X] (hp : p.Prime) (hodd : Odd p)
    (hoddX : Odd (Nat.card X)) (hpX : p ∣ Nat.card X) (P : Sylow p X)
    (hnarrow : IsPNarrow p ↥(P : Subgroup X)) (hlen : HasPLengthLeOne p X) :
    pComplCore p ↥(commutator X)
      = (pComplCore p X ⊓ commutator X).subgroupOf (commutator X) :=
  have := Fact.mk hp
  ((isNormalPComplement_inf_commutator (P := (P : Subgroup X)) hp hoddX hpX
    P.card_eq_multiplicity (hasPLengthLeOne_iff_not_dvd_index_pComplPCore.1 hlen)
    (isCyclic_or_maximal_plane_of_isPNarrow hp hodd P.isPGroup' hnarrow)).eq_pComplCore hp).symm

end

end CFSG.FeitThompson
