module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqPer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqDiv

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Blueprint CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof

theorem cl24_cross (hO : LieOrderFormulasInput) {Q : Type} [Group Q] {τ τ' : StatedLieTag}
    {n n' j d : ℕ} (h : LieModel Q τ n 3 j) (h' : LieModel Q τ' n' 3 d) :
    lieSylowExponent τ n * j = lieSylowExponent τ' n' * d ∧
      lieOrderCofactor τ n (3 ^ j) * lieOrderDivisor τ' n' (3 ^ d) =
        lieOrderCofactor τ' n' (3 ^ d) * lieOrderDivisor τ n (3 ^ j) := by
  obtain ⟨-, hnum, hfac⟩ := hO Q τ n 3 j h.admissible h
  obtain ⟨-, hnum', hfac'⟩ := hO Q τ' n' 3 d h'.admissible h'
  have hN : lieSylowExponent τ n * j = lieSylowExponent τ' n' * d := hfac.symm.trans hfac'
  refine ⟨hN, ?_⟩
  rw [lieOrderNumerator_eq h.admissible] at hnum
  rw [lieOrderNumerator_eq h'.admissible] at hnum'
  have hP : (3 ^ j) ^ lieSylowExponent τ n = (3 ^ d) ^ lieSylowExponent τ' n' := by
    rw [← pow_mul, ← pow_mul, mul_comm j, mul_comm d, hN]
  have hP0 : 0 < (3 ^ j) ^ lieSylowExponent τ n := by positivity
  apply Nat.eq_of_mul_eq_mul_left hP0
  calc (3 ^ j) ^ lieSylowExponent τ n * (lieOrderCofactor τ n (3 ^ j) *
        lieOrderDivisor τ' n' (3 ^ d))
      = ((3 ^ j) ^ lieSylowExponent τ n * lieOrderCofactor τ n (3 ^ j)) *
          lieOrderDivisor τ' n' (3 ^ d) := by ring
    _ = (Nat.card Q * lieOrderDivisor τ n (3 ^ j)) * lieOrderDivisor τ' n' (3 ^ d) := by
        rw [hnum]
    _ = (Nat.card Q * lieOrderDivisor τ' n' (3 ^ d)) * lieOrderDivisor τ n (3 ^ j) := by ring
    _ = ((3 ^ d) ^ lieSylowExponent τ' n' * lieOrderCofactor τ' n' (3 ^ d)) *
          lieOrderDivisor τ n (3 ^ j) := by rw [hnum']
    _ = (3 ^ j) ^ lieSylowExponent τ n * (lieOrderCofactor τ' n' (3 ^ d) *
          lieOrderDivisor τ n (3 ^ j)) := by rw [hP]; ring

theorem cl24_E_le {τ τ' : StatedLieTag} {n n' j d : ℕ} (hadm : StatedLieAdmissible τ n 3 j)
    (hadm' : StatedLieAdmissible τ' n' 3 d)
    (hC : lieOrderCofactor τ n (3 ^ j) * lieOrderDivisor τ' n' (3 ^ d) =
      lieOrderCofactor τ' n' (3 ^ d) * lieOrderDivisor τ n (3 ^ j)) :
    j * cl24E τ n ≤ d * cl24E τ' n' := by
  obtain ⟨ℓ, hℓ, h2, h3, hk⟩ := cl24_exists_ppd (cl24_three_le hadm)
  have hdC : ℓ ∣ lieOrderCofactor τ n (3 ^ j) := cl24_ppd_dvd hadm hℓ hk rfl
  have hdm : ℓ ∣ lieOrderCofactor τ' n' (3 ^ d) * lieOrderDivisor τ n (3 ^ j) :=
    hC ▸ dvd_mul_of_dvd_left hdC _
  have hnD : ¬ ℓ ∣ lieOrderDivisor τ n (3 ^ j) := by
    intro hD
    rcases cl24_prime_dvd_D hadm hℓ hD with h | h | ⟨h, hn⟩
    · exact h2 h
    · exact h3 h
    · have h1 : j * cl24E τ n ∣ j * 2 := by
        have := (hk (2 * j)).1 h
        rwa [mul_comm 2 j] at this
      have hj : 0 < j := hadm.2.1
      have h5 := Nat.le_of_dvd (by norm_num) (Nat.dvd_of_mul_dvd_mul_left hj h1)
      rcases cl24_E_three_le_or hadm with h6 | ⟨rfl, rfl⟩
      · omega
      · have := hn rfl
        omega
  rcases (Nat.Prime.dvd_mul hℓ).1 hdm with h | h
  · exact cl24_ppd_le hadm' hℓ hk h
  · exact absurd h hnD

theorem cl24_E_eq {τ τ' : StatedLieTag} {n n' j d : ℕ} (hadm : StatedLieAdmissible τ n 3 j)
    (hadm' : StatedLieAdmissible τ' n' 3 d)
    (hC : lieOrderCofactor τ n (3 ^ j) * lieOrderDivisor τ' n' (3 ^ d) =
      lieOrderCofactor τ' n' (3 ^ d) * lieOrderDivisor τ n (3 ^ j)) :
    j * cl24E τ n = d * cl24E τ' n' :=
  le_antisymm (cl24_E_le hadm hadm' hC) (cl24_E_le hadm' hadm hC.symm)

end CFSG.OddStandard.SmallF3.HypA2Leaves
