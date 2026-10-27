module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB4
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedQuaternion
public import CFSG.ClassicalInvolution.Q3.Q3T6LinEquiv

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped MatrixGroups

theorem sec5c3q_ne_two {p n : ℕ} (hn : 0 < n) (hq : p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) : p ≠ 2 := by
  rintro rfl
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : 2 ^ (m + 1) % 2 = 0 := by
    rw [pow_succ]
    exact Nat.mul_mod_left _ _
  omega

theorem sec5c3q_exists_quaternion_sylow {p n : ℕ} [Fact p.Prime] (hn : 0 < n)
    (hq : p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) {K : Type} [Group K] [Finite K]
    (e : K ⧸ CFSG.Open.classicalInvolutionOddCore K ≃* SL(2, GaloisField p n)) (T : Sylow 2 K) :
    ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((T : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn.ne'
  by_cases h3 : p ^ n = 3
  · exact CFSG.ClassicalInvolution.Q3.Q3T6.exists_quaternion_of_sl2_three' (hcard.trans h3) e T
  · have h5 : 5 ≤ Nat.card (GaloisField p n) := by
      rw [hcard]
      omega
    have hodd : Odd (Nat.card (GaloisField p n)) := by
      rw [hcard, Nat.odd_iff]
      omega
    exact CFSG.ClassicalInvolution.Disconnected.exists_quaternion_of_sl2 hodd h5 e T

theorem sec5c3q_quaternion_of_isSL2qMod {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (hq : p ^ n % 8 = 3 ∨ p ^ n % 8 = 5)
    (h : IsSL2qMod K p n) (T : Sylow 2 ↥K) :
    ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((T : Subgroup ↥K) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨e⟩ := h
  have hO : CFSG.Open.classicalInvolutionOddCore ↥K = CFSG.oddCore ↥K := rfl
  exact sec5c3q_exists_quaternion_sylow hn hq ((QuotientGroup.quotientMulEquivOfEq hO).trans e) T

theorem sec5c3q_witness_of_isSL2qMod {G : Type} [Group G] {K : Subgroup G} {p n : ℕ}
    [Fact p.Prime] (hn : 0 < n) (hq : p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) (h : IsSL2qMod K p n) :
    CFSG.Open.classicalInvolutionWitness K := by
  obtain ⟨e⟩ := h
  have hO : CFSG.Open.classicalInvolutionOddCore ↥K = CFSG.oddCore ↥K := rfl
  exact Or.inl ⟨p, n, inferInstance, sec5c3q_ne_two hn hq, hn,
    ⟨(QuotientGroup.quotientMulEquivOfEq hO).trans e⟩⟩

end CFSG.OddStandard.SmallF3.Omega
