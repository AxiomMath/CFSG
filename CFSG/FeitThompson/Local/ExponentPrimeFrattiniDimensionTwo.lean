module

public import Mathlib.GroupTheory.Frattini
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Local.FrattiniQuotientPPowerElementaryAbelian
import CFSG.FeitThompson.Local.ExponentPrimeRankTwoOrderCube

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p a : ℕ} {P : Type*} [Group P]

theorem frattini_ne_top [Finite P] [Nontrivial P] : frattini P ≠ ⊤ := fun h =>
  bot_ne_top (frattini_nongenerating (K := (⊥ : Subgroup P)) (by rw [h, bot_sup_eq]))

theorem exists_mulEquiv_quotient_frattini_of_elementaryAbelianPRank_le_two [Finite P] [Nontrivial P]
    (hp : p.Prime) (hrank : elementaryAbelianPRank p P ≤ 2) (hexp : ∀ x : P, x ^ p = 1) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ 2 ∧ Nat.card (P ⧸ frattini P) = p ^ d ∧
      Nonempty ((P ⧸ frattini P) ≃* (Fin d → Multiplicative (ZMod p))) := by
  have := Fact.mk hp
  have hP : IsPGroup p P := isPGroup_of_forall_pow_eq_one hexp
  obtain ⟨d, hcard, he⟩ := exists_mulEquiv_quotient_frattini_of_isPGroup hp hP
  have hidx : (frattini P).index = p ^ d := by rw [Subgroup.index_eq_card, hcard]
  have hmul : Nat.card (frattini P) * p ^ d = Nat.card P := by
    rw [← hidx]; exact (frattini P).card_mul_index
  refine ⟨d, ?_, ?_, hcard, he⟩
  ·
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact absurd (Subgroup.index_eq_one.1 (by simpa using hidx)) frattini_ne_top
    · exact hd
  ·
    have hle : Nat.card P ≤ p ^ 3 :=
      card_le_pow_three_of_elementaryAbelianPRank_le_two hp hrank hexp
    have hpd : p ^ d ≤ p ^ 3 := by
      refine le_trans ?_ hle
      rw [← hmul]
      exact Nat.le_mul_of_pos_left _ Nat.card_pos
    have hd3 : d ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).1 hpd
    by_contra hc
    obtain rfl : d = 3 := by omega
    have hone : Nat.card (frattini P) = 1 := by
      have h1 : Nat.card (frattini P) * p ^ 3 ≤ 1 * p ^ 3 := by rw [one_mul, hmul]; exact hle
      have := Nat.le_of_mul_le_mul_right h1 (pow_pos hp.pos 3)
      have := Nat.card_pos (α := frattini P)
      omega
    have hbot : frattini P = ⊥ := Subgroup.card_eq_one.1 hone
    obtain ⟨e⟩ := he
    have e0 : P ≃* (P ⧸ frattini P) :=
      (QuotientGroup.quotientBot (G := P)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hbot.symm)
    have h3 : (3 : ℕ) ∈ elementaryAbelianRanks p P :=
      mem_elementaryAbelianRanks.2 ⟨⊤, ⟨Subgroup.topEquiv.trans (e0.trans e)⟩⟩
    have := le_elementaryAbelianPRank hp.one_lt h3
    omega

theorem exists_mulEquiv_quotient_frattini_of_card_eq_pow_of_elementaryAbelianPRank_le_two
    [Nontrivial P] (hp : p.Prime) (hcard : Nat.card P = p ^ a)
    (hrank : elementaryAbelianPRank p P ≤ 2) (hexp : ∀ x : P, x ^ p = 1) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ 2 ∧ Nat.card (P ⧸ frattini P) = p ^ d ∧
      Nonempty ((P ⧸ frattini P) ≃* (Fin d → Multiplicative (ZMod p))) :=
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  exists_mulEquiv_quotient_frattini_of_elementaryAbelianPRank_le_two hp hrank hexp

theorem card_quotient_frattini_le_sq_of_elementaryAbelianPRank_le_two [Finite P] [Nontrivial P]
    (hp : p.Prime) (hrank : elementaryAbelianPRank p P ≤ 2) (hexp : ∀ x : P, x ^ p = 1) :
    p ≤ Nat.card (P ⧸ frattini P) ∧ Nat.card (P ⧸ frattini P) ≤ p ^ 2 := by
  obtain ⟨d, hd1, hd2, hcard, -⟩ :=
    exists_mulEquiv_quotient_frattini_of_elementaryAbelianPRank_le_two hp hrank hexp
  rw [hcard]
  exact ⟨by simpa using Nat.pow_le_pow_right hp.pos hd1, Nat.pow_le_pow_right hp.pos hd2⟩

end

end CFSG.FeitThompson
