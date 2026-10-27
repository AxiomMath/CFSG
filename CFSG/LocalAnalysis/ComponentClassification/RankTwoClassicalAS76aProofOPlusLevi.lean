module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOChoice

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

section Forms

variable {K : Type} [Field K]

theorem statedQuadPlus_smul (k : ℕ) (d : K) (w : Fin k ⊕ Fin k → K) :
    StatedQuadPlus k K (d • w) = d * d * StatedQuadPlus k K w := by
  rw [← coe_quadPlus, QuadraticMap.map_smul, smul_eq_mul]

@[expose] def plusVec {k : ℕ} (hk : 1 ≤ k) : Fin k ⊕ Fin k → K :=
  Pi.single (.inl ⟨0, hk⟩) 1 + Pi.single (.inr ⟨0, hk⟩) 1

theorem statedQuadPlus_plusVec {k : ℕ} (hk : 1 ≤ k) : StatedQuadPlus k K (plusVec hk) = 1 := by
  simp [StatedQuadPlus, plusVec, Pi.single_apply]

theorem oProj_injective_plus [CharP K 2] {k : ℕ} (hk : 1 ≤ k) :
    Function.Injective (oProj (StatedQuadPlus k K)) :=
  oProj_injective (v₀ := plusVec hk) (by rw [statedQuadPlus_plusVec]; exact one_ne_zero)
    fun c => statedQuadPlus_smul k c _

theorem odd_card_center_statedOmega_quadPlus [CharP K 2] {k : ℕ} (hk : 3 ≤ k) :
    Odd (Nat.card (center (StatedOmega (StatedQuadPlus k K)))) := by
  rw [card_center_statedOmega_eq_one (center_statedOmega_quadPlus hk)
    (oProj_injective_plus (by omega))]
  exact odd_one

theorem commutant_statedOmega_quadPlus [Finite K] (hK : 2 < Nat.card K) {k : ℕ} (hk : 2 ≤ k)
    (Y : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) K)
    (hY : ∀ Z ∈ StatedOmega (StatedQuadPlus k K),
      Y * (Z : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) K) = (Z : Matrix _ _ K) * Y) :
    ∃ d : K, Y = d • 1 :=
  eq_smul_one_of_commute_statedOmega hK (quadPlus k K) (nondegenerate_polarBilin_quadPlus k K)
    (by simp; omega) (by rw [coe_quadPlus]; exact hY)

end Forms

section Field

variable {K : Type} [Field K] [Finite K] {m : ℕ}

omit [Field K] [Finite K] in
theorem four_le_card (hK : Nat.card K = 2 ^ m) (hm : 2 ≤ m) : 4 ≤ Nat.card K := by
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

omit [Field K] in
theorem exists_finset_four (h4 : 4 ≤ Nat.card K) : ∃ s : Finset K, s.card = 4 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  exact ⟨s, hs⟩

omit [Finite K] in
theorem exists_ne_zero_ne_one (h4 : 4 ≤ Nat.card K) : ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective (fun t : Bool => if t then (1 : K) else 0) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨false, by simp [hx]⟩
    · exact ⟨true, by simp [hcon x hx]⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

end Field

end CFSG.ComponentClassification.RankTwoClassical
