module

public import CFSG.HardMathSupport.Solomon.Coordinator.B2OddCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

namespace B2FamAlt

theorem isSolvable_of_card_dvd_168 {H : Type*} [Group H] [Finite H] (h1 : Nat.card H ∣ 168)
    (h2 : Nat.card H ≤ 24) : Group.IsSolvable H := by
  have : Fintype H := Fintype.ofFinite H
  have key : ∃ p q a b : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ Nat.card H = p ^ a * q ^ b := by
    have hmem : Nat.card H ∈ (Finset.range 25).filter (· ∣ 168) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h1⟩
    have hset : (Finset.range 25).filter (· ∣ 168) = {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24} := by
      decide
    rw [hset] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
    · exact ⟨2, 3, 0, 0, Nat.prime_two, Nat.prime_three, by norm_num, by norm_num⟩
    · exact ⟨2, 3, 1, 0, Nat.prime_two, Nat.prime_three, by norm_num, by norm_num⟩
    · exact ⟨2, 3, 0, 1, Nat.prime_two, Nat.prime_three, by norm_num, by norm_num⟩
    · exact ⟨2, 3, 2, 0, Nat.prime_two, Nat.prime_three, by norm_num, by norm_num⟩
    · exact ⟨2, 3, 1, 1, Nat.prime_two, Nat.prime_three, by norm_num, by norm_num⟩
    · exact ⟨2, 7, 0, 1, Nat.prime_two, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨2, 3, 3, 0, Nat.prime_two, Nat.prime_three, by norm_num, by norm_num⟩
    · exact ⟨2, 3, 2, 1, Nat.prime_two, Nat.prime_three, by norm_num, by norm_num⟩
    · exact ⟨2, 7, 1, 1, Nat.prime_two, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 7, 1, 1, Nat.prime_three, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨2, 3, 3, 1, Nat.prime_two, Nat.prime_three, by norm_num, by norm_num⟩
  obtain ⟨p, q, a, b, hp, hq, hpq, hc⟩ := key
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card, hc])

theorem card_dvd_factorial_index {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    {H : Subgroup S} (hH : H ≠ ⊤) : Nat.card S ∣ (H.index).factorial := by
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (eq_top_iff.2 (h ▸ Subgroup.normalCore_le H)) hH
  have hinj : Function.Injective (MulAction.toPermHom S (S ⧸ H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  have hdvd : Nat.card S ∣ Nat.card (Equiv.Perm (S ⧸ H)) :=
    Subgroup.card_dvd_of_injective _ hinj
  rwa [Nat.card_perm, ← Subgroup.index_eq_card] at hdvd

theorem isSolvable_of_card_168 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : Nat.card S = 168) {H : Subgroup S} (hH : H ≠ ⊤) : Group.IsSolvable H := by
  have hfac := card_dvd_factorial_index hH
  rw [hS] at hfac
  have hmul := Subgroup.card_mul_index H
  rw [hS] at hmul
  have hidx1 : H.index ≠ 1 := fun h => hH (Subgroup.index_eq_one.1 h)
  have hidx0 : H.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul
    omega
  have hidx : 7 ≤ H.index := by
    by_contra hlt
    push_neg at hlt
    interval_cases h : H.index <;> simp_all [Nat.factorial] <;> omega
  refine isSolvable_of_card_dvd_168 ⟨H.index, by rw [← hmul, mul_comm]⟩ ?_
  by_contra hgt
  push_neg at hgt
  have : 25 * 7 ≤ Nat.card H * H.index := Nat.mul_le_mul (by omega) hidx
  omega

theorem commutator_eq_bot_of_card_168 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (hS : Nat.card S = 168) (β : MulAut S) :
    ⁅GLAPLayer 2 (fixSubgroup β), GLAPPrimeCoreOf 2 (fixSubgroup β)⁆ = ⊥ := by
  by_cases h1 : β = 1
  · exact commutator_eq_bot_of_oddCore hnc β fun h => absurd h1 h
  refine commutator_eq_bot_of_isSolvable β (isSolvable_of_card_168 hS fun htop => h1 ?_)
  ext s
  have : s ∈ fixSubgroup β := htop ▸ Subgroup.mem_top s
  exact this

end B2FamAlt

end CFSG.HardMathSupport.Solomon.Coordinator
