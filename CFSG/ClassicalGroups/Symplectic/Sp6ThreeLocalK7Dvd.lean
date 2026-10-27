module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalBlockCommute
public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalLevi
public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalOrthTorus

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem dvd_sq_sub_one_of_dvd_qPlusPi {q p : ℕ}
    (hpq : p ∣ if q % 3 = 1 then q + 1 else q - 1) : p ∣ q ^ 2 - 1 := by
  have h : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      apply Nat.sub_eq_of_eq_add
      ring
  split_ifs at hpq
  · rw [h]
    exact Dvd.dvd.mul_right hpq _
  · rw [h]
    exact Dvd.dvd.mul_left hpq _

theorem dvd_card_centralizer_c₀_weight_one [Finite K] {p : ℕ} (hp : p.Prime) {s : SL(2, K)}
    (hs : IsCubeRootBlock s) (hpq : p ∣ Nat.card K ^ 2 - 1) :
    p ∣ Nat.card (Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 0, 0])} : Set (StatedSp 3 K))) := by
  obtain ⟨z, hz⟩ := exists_orderOf_eq_specialLinearGroup (K := K) hp hpq
  have hmem : block (Pi.mulSingle 2 z) ∈ Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 0, 0])} : Set (StatedSp 3 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_block_mulSingle_c₀ (i := 2) hs z (Multiplicative.ofAdd ![1, 0, 0])
      (by simp)).eq
  have := Subgroup.orderOf_dvd_natCard _ hmem
  rwa [orderOf_block_mulSingle, hz] at this

theorem dvd_card_centralizer_c₀_weight_two [Finite K] {p : ℕ} (hp : p.Prime) {s : SL(2, K)}
    (hs : IsCubeRootBlock s) (hpq : p ∣ Nat.card K ^ 2 - 1) :
    p ∣ Nat.card (Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 1, 0])} : Set (StatedSp 3 K))) := by
  obtain ⟨z, hz⟩ := exists_orderOf_eq_specialLinearGroup (K := K) hp hpq
  have hmem : block (Pi.mulSingle 2 z) ∈ Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 1, 0])} : Set (StatedSp 3 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_block_mulSingle_c₀ (i := 2) hs z (Multiplicative.ofAdd ![1, 1, 0])
      (by simp)).eq
  have := Subgroup.orderOf_dvd_natCard _ hmem
  rwa [orderOf_block_mulSingle, hz] at this

theorem dvd_card_centralizer_std_weight_one [Finite K] (h3 : (3 : K) ≠ 0) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ if Nat.card K % 3 = 1 then Nat.card K + 1 else Nat.card K - 1) :
    p ∣ Nat.card (Subgroup.centralizer
      ({c₀ (isCubeRootBlock_cubeRootBlockStd h3) (Multiplicative.ofAdd ![1, 0, 0])} :
        Set (StatedSp 3 K))) :=
  dvd_card_centralizer_c₀_weight_one hp (isCubeRootBlock_cubeRootBlockStd h3)
    (dvd_sq_sub_one_of_dvd_qPlusPi hpq)

theorem dvd_card_centralizer_std_weight_two [Finite K] (h3 : (3 : K) ≠ 0) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ if Nat.card K % 3 = 1 then Nat.card K + 1 else Nat.card K - 1) :
    p ∣ Nat.card (Subgroup.centralizer
      ({c₀ (isCubeRootBlock_cubeRootBlockStd h3) (Multiplicative.ofAdd ![1, 1, 0])} :
        Set (StatedSp 3 K))) :=
  dvd_card_centralizer_c₀_weight_two hp (isCubeRootBlock_cubeRootBlockStd h3)
    (dvd_sq_sub_one_of_dvd_qPlusPi hpq)

theorem dvd_card_centralizer_std_weight_three [Finite K] (h3 : (3 : K) ≠ 0) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ if Nat.card K % 3 = 1 then Nat.card K + 1 else Nat.card K - 1) :
    p ∣ Nat.card (Subgroup.centralizer
      ({c₀ (isCubeRootBlock_cubeRootBlockStd h3) (Multiplicative.ofAdd ![1, 1, 1])} :
        Set (StatedSp 3 K))) := by
  by_cases hq : Nat.card K % 3 = 1
  · rw [if_pos hq] at hpq
    obtain ⟨ω, -, hω⟩ := cubeRootBlockStd_eq_cubeRootDiag h3 hq
    exact dvd_card_centralizer_c₀_weight_three_of_dvd_add_one
      (isCubeRootBlock_cubeRootBlockStd h3) hω hp hpq
  · rw [if_neg hq] at hpq
    exact dvd_card_centralizer_c₀_weight_three_of_dvd_sub_one
      (isCubeRootBlock_cubeRootBlockStd h3) hp hpq

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
