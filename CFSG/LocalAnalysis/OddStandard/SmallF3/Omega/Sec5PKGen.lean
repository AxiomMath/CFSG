module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTGen

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sec5pk_twoRes_eq {K : Subgroup G} (hK : IsSL23Mod K) : twoRes K = K := by
  apply le_antisymm
  · rw [twoRes]
    exact (Subgroup.closure_le K).mpr fun g hg => hg.1
  · rw [twoRes]
    exact l34g_le_closure_odd (C := G) (B := K) hK

theorem sec5pk_orderOf_three_pow {K : Subgroup G} (hK : IsSL23Mod K)
    (hO : IsPGroup 3 (oddCoreIn K)) :
    ∀ k ∈ K, Odd (orderOf k) → ∃ n : ℕ, orderOf k = 3 ^ n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hK
  intro k hkK hkodd
  have hquot : Nat.card (↥K ⧸ CFSG.oddCore ↥K) = 24 := by
    rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field 2]
    simp [ZMod.card, Fin.prod_univ_two]
  have hcore : Nat.card (oddCoreIn K) = Nat.card (CFSG.oddCore ↥K) := by
    rw [oddCoreIn, CFSG.inSubgroup]
    exact Subgroup.card_map_of_injective K.subtype_injective
  have hcard : Nat.card ↥K = 24 * Nat.card (oddCoreIn K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K), hquot,
      ← hcore]
  obtain ⟨m, hm⟩ := hO.exists_card_eq
  have hcard' : Nat.card ↥K = 2 ^ 3 * 3 ^ (m + 1) := by
    rw [hcard, hm, show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, mul_assoc, ← pow_succ']
  have hdivK : orderOf k ∣ Nat.card ↥K := Subgroup.orderOf_dvd_natCard K hkK
  have hdiv : orderOf k ∣ 2 ^ 3 * 3 ^ (m + 1) := by rwa [hcard'] at hdivK
  have hcop : Nat.Coprime (orderOf k) (2 ^ 3) :=
    (Nat.coprime_pow_right_iff (by norm_num) (orderOf k) 2).mpr
      (Nat.coprime_two_right.mpr hkodd)
  have h3 : orderOf k ∣ 3 ^ (m + 1) := hcop.dvd_of_dvd_mul_left hdiv
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h3
  exact ⟨n, hn⟩

end CFSG.OddStandard.SmallF3.Omega
