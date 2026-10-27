module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HN
public import CFSG.Sporadic.HNSchreier.ThreeCheckInputs
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public meta import CFSG.Sporadic.HNSchreier.FAData
public import CFSG.Sporadic.HNSchreier.ThreeSpec
public import Certificates.Certificate13602

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Perm.Native

theorem hnThreeWitness_of_certificate :
    HNThreeWitness := by
  obtain ⟨hU5, hU1, hk⟩ := Certificates.certificate13602
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf (g3J ^ 6) = 5 := orderOf_eq_prime hU5 hU1
  have hmem : g3J ^ 6 ∈ CJ (sJ 2) := pow_mem g3J_mem_CJ 6
  have hg : c3J 0 ∈ CJ (sJ 2) := mem_CJ.2 (c3J_comm (j := 0) (by norm_num)).symm
  refine ⟨g3J ^ 6, c3J 0, hmem, hord, hg, fun hz => ?_⟩
  obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hmod : (g3J ^ 6) ^ k = (g3J ^ 6) ^ (k % 5).toNat := by
    have h := zpow_eq_zpow_emod' (x := g3J ^ 6) k hU5
    have h0 : 0 ≤ k % 5 := Int.emod_nonneg _ (by norm_num)
    have hjk : (k % (5 : ℕ) : ℤ) = (((k % 5).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0]; norm_num
    rw [h, hjk, zpow_natCast]
  obtain ⟨j, hjdef⟩ : ∃ j, j = (k % 5).toNat := ⟨_, rfl⟩
  have hj5 : j < 5 := by omega
  rw [← hjdef] at hmod
  have hgu : c3J 0 * g3J ^ 6 = (g3J ^ 6) ^ j * c3J 0 := by
    have : (g3J ^ 6) ^ j = c3J 0 * g3J ^ 6 * (c3J 0)⁻¹ := hmod.symm.trans hk'
    rw [this]; group
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · apply hU1
    simpa using hgu
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact hk j' (by omega) hgu

theorem sporadicOPrimeHolds_HN_three :
    SporadicOPrimeHolds .HN 3 :=
  sporadicOPrimeHolds_HN_three_of_witness hnThreeWitness_of_certificate

theorem sporadicOnePairHolds_HN_three :
    SporadicOnePairHolds .HN 3 :=
  ⟨sporadicOPrimeHolds_HN_three, sporadicOuterHolds_HN_three⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
