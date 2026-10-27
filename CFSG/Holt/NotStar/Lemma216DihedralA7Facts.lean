module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.Holt.NotStar216

open Equiv Equiv.Perm

theorem cycleType_eq_two_two {σ : Perm (Fin 7)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1)
    (hs : sign σ = 1) : σ.cycleType = {2, 2} := by
  have hmem : ∀ k ∈ σ.cycleType, k = 2 := fun k hk => by
    have hk2 := two_le_of_mem_cycleType hk
    have hdvd := (dvd_of_mem_cycleType hk).trans (orderOf_dvd_of_pow_eq_one h2)
    have := Nat.le_of_dvd two_pos hdvd
    omega
  have hrep := Multiset.eq_replicate_card.mpr hmem
  have hsum := sum_cycleType_le σ
  have hsign := sign_of_cycleType σ
  rw [hrep] at hsum hsign
  rw [hrep]
  rw [Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  rw [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul, hs] at hsign
  have hm0 : Multiset.card σ.cycleType ≠ 0 := fun h =>
    h1 (cycleType_eq_zero.mp (by rw [hrep, h, Multiset.replicate_zero]))
  generalize Multiset.card σ.cycleType = m at hsum hsign hm0 ⊢
  have hm3 : m ≤ 3 := by omega
  interval_cases m
  · exact absurd rfl hm0
  · exact absurd hsign (by decide)
  · rfl
  · exact absurd hsign (by decide)

theorem card_centralizer_of_involution {σ : Perm (Fin 7)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1)
    (hs : sign σ = 1) : Nat.card (Subgroup.centralizer {σ}) = 48 := by
  rw [nat_card_centralizer, cycleType_eq_two_two h2 h1 hs]
  decide

end CFSG.Holt.NotStar216
