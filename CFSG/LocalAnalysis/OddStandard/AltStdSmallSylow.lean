module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarPerm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.AltStdSmall

open Equiv Equiv.Perm Subgroup

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem two_mul_card_centralizer_inf_alternating {c : Perm α} (hc2 : c * c = 1) (hc1 : c ≠ 1) :
    2 * Nat.card (alternatingGroup α ⊓ centralizer ({c} : Set (Perm α)) : Subgroup (Perm α)) =
      Nat.card (centralizer ({c} : Set (Perm α))) := by
  obtain ⟨a, ha⟩ : ∃ a, c a ≠ a := by
    by_contra hne
    push Not at hne
    exact hc1 (Equiv.ext hne)
  have hca : c (c a) = a := by
    have := congrArg (fun f : Perm α => f a) hc2
    simpa using this
  set s := swap a (c a) with hs
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hsC : s ∈ centralizer ({c} : Set (Perm α)) := by
    rw [mem_centralizer_singleton_iff, hs, swap_mul_eq_mul_swap, hcinv, hca, swap_comm]
  have hsA : s ∉ alternatingGroup α := by
    rw [mem_alternatingGroup, hs, sign_swap (Ne.symm ha)]
    decide
  have hrel : (alternatingGroup α).relIndex (centralizer ({c} : Set (Perm α))) = 2 := by
    rw [relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨s, hsC, hsA, fun b _ => ?_⟩
    by_cases hb : b ∈ alternatingGroup α
    · exact Or.inr hb
    · left
      rw [mem_alternatingGroup] at hb hsA ⊢
      rw [map_mul]
      rcases Int.units_eq_one_or (sign b) with h1 | h1
      · exact absurd h1 hb
      rcases Int.units_eq_one_or (sign s) with h2 | h2
      · exact absurd h2 hsA
      rw [h1, h2]
      decide
  have := relIndex_mul_card (H := alternatingGroup α) (K := centralizer ({c} : Set (Perm α)))
  rw [hrel] at this
  exact this

theorem sign_eq_neg_one_pow_of_mul_self {c : Perm α} (hc2 : c * c = 1) :
    sign c = (-1 : ℤˣ) ^ Multiset.card c.cycleType := by
  rw [sign_of_cycleType, AltStdSec.cycleType_eq_replicate_two hc2, Multiset.sum_replicate,
    Multiset.card_replicate, smul_eq_mul, pow_add, pow_mul, Int.units_sq, one_mul]

theorem support_card_eq_eight_of_comm_sym (hn8 : 8 ≤ Fintype.card α) (hn9 : Fintype.card α ≤ 9)
    {P : Subgroup (Perm α)} (hP : 2 ^ 7 ∣ Nat.card P) {c : Perm α} (hc2 : c * c = 1)
    (hc1 : c ≠ 1) (hPc : ∀ p ∈ P, p * c = c * p) : c.support.card = 8 := by
  have hle : P ≤ centralizer ({c} : Set (Perm α)) :=
    fun p hp => mem_centralizer_singleton_iff.2 (hPc p hp)
  have h1 := Subgroup.card_dvd_of_le hle
  rw [AltStdSec.nat_card_centralizer_of_mul_self hc2] at h1
  have hdvd := hP.trans h1
  have hs := AltStdSec.card_support_eq_two_mul_card_cycleType hc2
  have hsl : c.support.card ≤ Fintype.card α := Finset.card_le_univ _
  have hk0 : Multiset.card c.cycleType ≠ 0 := by
    intro h0
    rw [h0, mul_zero, Finset.card_eq_zero, support_eq_empty_iff] at hs
    exact hc1 hs
  rw [hs]
  obtain ⟨k, hk⟩ : ∃ k, Multiset.card c.cycleType = k := ⟨_, rfl⟩
  rw [hk] at hdvd hs hk0
  rw [hs] at hsl
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card α = m := ⟨_, rfl⟩
  rw [hm] at hdvd hsl hn8 hn9
  have hk4 : k ≤ 4 := by omega
  interval_cases m <;> interval_cases k <;> first
    | rfl
    | omega
    | (exfalso; revert hdvd; decide)

end Perm

end CFSG.OddStandard.AltStdSmall
