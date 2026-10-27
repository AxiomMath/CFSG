module

public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement

theorem center_eq_bot_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  obtain ⟨a, b, hab⟩ := hS
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact absurd (mem_center_iff.1 (h ▸ mem_top b) a) hab

theorem isQuasisimple_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) : CFSG.IsQuasisimple S := by
  have hZ := center_eq_bot_of_isSimpleGroup hS
  obtain ⟨a, b, hab⟩ := hS
  have hperf : Group.IsPerfect S := by
    refine ⟨?_⟩
    rcases (Subgroup.commutator_normal (⊤ : Subgroup S) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      apply hab
      have hc : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup S), ⊤⁆ :=
        commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · rw [_root_.commutator_def]
      exact h
  let e : S ⧸ center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : IsSimpleGroup (S ⧸ center S) := e.isSimpleGroup
  refine ⟨hperf, this, e.symm a, e.symm b, fun h => hab (e.symm.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem two_le_pRank_of_isQuasisimple_of_odd_center {R : Type*} [Group R] [Finite R]
    (hR : CFSG.IsQuasisimple R) (hZR : Odd (Nat.card (center R))) : 2 ≤ CFSG.pRank 2 R := by
  by_contra hlt
  obtain ⟨-, ⟨z, hz, -⟩, hcen, -⟩ :=
    quasisimple_rank_one_unique_central_involution hR (by omega)
  have hdvd : orderOf (⟨z, hcen z hz⟩ : center R) ∣ Nat.card (center R) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hz] at hdvd
  exact (Nat.not_even_iff_odd.2 hZR) (even_iff_two_dvd.2 hdvd)

theorem exists_four_group_of_two_le_pRank {R : Type*} [Group R] [Finite R]
    (h2 : 2 ≤ CFSG.pRank 2 R) :
    ∃ A : Subgroup R, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h2
  exact ⟨E, hE, by rw [hcard]; norm_num⟩

theorem quasisimple_odd_center_fixed_four_group_rank {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) (hZ : Odd (Nat.card (center Q))) :
    (∃ A : Subgroup Q, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4) ∧
      2 ≤ CFSG.pRank 2 Q ∧
      ∀ (S : Type*) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
        ∃ A : Subgroup S, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
  have h2 := two_le_pRank_of_isQuasisimple_of_odd_center hQ hZ
  refine ⟨exists_four_group_of_two_le_pRank h2, h2, fun S _ _ _ hS => ?_⟩
  refine exists_four_group_of_two_le_pRank
    (two_le_pRank_of_isQuasisimple_of_odd_center (isQuasisimple_of_isSimpleGroup hS) ?_)
  rw [center_eq_bot_of_isSimpleGroup hS, Subgroup.card_bot]
  exact odd_one

end CFSG.LocalAnalysis.ComponentInitial
