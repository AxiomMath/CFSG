module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueSwap
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2SwapUniquePair

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {n : ℕ} {K : Type} [Field K]

theorem factorization_two_mul_card_mulAut_statedSp_two_le [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (hK : Nat.card K = 2) :
    (2 * Nat.card (MulAut (StatedSp n K))).factorization 2 ≤ n ^ 2 + 1 := by
  have : NeZero n := ⟨by omega⟩
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have hA : Nat.card (MulAut (StatedSp n K)) =
      Nat.card (MulAut (StatedProj (StatedSp n K))) :=
    Nat.card_congr (MulAut.congr (F4Pilot.spProjEquiv n K)).toEquiv
  have h2 := E6Pilot.card_mulAut_dvd_card_mul_card_outer (StatedProj (StatedSp n K))
  have h3 := (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.outer_card_dvd Nat.prime_two
    le_rfl hK1 (by omega)).2 hn
  rw [gcd_two_two_pow_sub_one le_rfl, mul_one] at h3
  have hP : Nat.card (StatedProj (StatedSp n K)) = Nat.card (StatedSp n K) :=
    (Nat.card_congr (F4Pilot.spProjEquiv n K).toEquiv).symm
  have h4 : 2 * Nat.card (MulAut (StatedSp n K)) ∣ 2 * Nat.card (StatedSp n K) := by
    rw [hA, ← hP]
    refine Nat.mul_dvd_mul_left 2 (h2.trans ?_)
    rw [Nat.dvd_one.1 h3, mul_one]
  have hS0 : Nat.card (StatedSp n K) ≠ 0 := Nat.card_pos.ne'
  have hA0 : 2 * Nat.card (MulAut (StatedSp n K)) ≠ 0 := by
    refine mul_ne_zero two_ne_zero ?_
    rw [hA]
    have : Finite (StatedProj (StatedSp n K)) :=
      Finite.of_equiv _ (F4Pilot.spProjEquiv n K).toEquiv
    exact Nat.card_pos.ne'
  have h5 := (Nat.factorization_le_iff_dvd hA0 (mul_ne_zero two_ne_zero hS0)).2 h4 2
  rw [Nat.factorization_mul two_ne_zero hS0, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two,
    factorization_card_statedSp (by omega) hK1 le_rfl, one_mul] at h5
  omega

theorem le_factorization_card_fixedSubgroup_statedSp_two [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (hK : Nat.card K = 2) {θ : MulAut (StatedSp n K)} (hθ : θ * θ = 1) :
    n * (n + 1) / 2 ≤ (Nat.card (fixedSubgroup θ)).factorization 2 := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  rcases involution_dichotomy_sp hn hK1 hθ with h | ⟨k, hk, -, -⟩
  · rwa [one_mul] at h
  · exfalso
    rw [hK] at hk
    have hk1 : 1 ≤ Nat.card k := Nat.card_pos
    rcases Nat.lt_or_ge (Nat.card k) 2 with h2 | h2
    · have : Nat.card k = 1 := by omega
      rw [this] at hk
      norm_num at hk
    · nlinarith

theorem swapPairExclusion_statedSp_two [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (hK : Nat.card K = 2) : SeitzQ2.SwapPairExclusion (StatedSp n K) := by
  intro θ θ' hθ _ hθ' _ h2 _
  have h1 := le_factorization_card_fixedSubgroup_statedSp_two hn hK hθ
  have h1' := le_factorization_card_fixedSubgroup_statedSp_two hn hK hθ'
  have hA := factorization_two_mul_card_mulAut_statedSp_two_le hn hK
  have hnn : n * (n + 1) / 2 * 2 = n * (n + 1) :=
    Nat.div_mul_cancel (Nat.even_mul_succ_self n).two_dvd
  have : n * (n + 1) ≤ n ^ 2 + 1 := by omega
  nlinarith

end CFSG.SeitzReduction.SymplecticPilot
