module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2More
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16Dyn

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace Unc25K1

theorem fermat_or_mersenne_pow {p : ℕ} (hFM : IsFermatOrMersenne p) (h7 : 7 < p) :
    (p % 8 = 1 ∧ ∃ m : ℕ, p = 2 ^ m + 1) ∨ (p % 8 = 7 ∧ ∃ m : ℕ, p + 1 = 2 ^ m) := by
  rcases hFM.2 with ⟨k, hk⟩ | ⟨k, hk2, hk⟩
  · left
    refine ⟨?_, 2 ^ k, hk⟩
    have h3 : 3 ≤ 2 ^ k := by
      by_contra hlt
      have h2k : 2 ^ k ≤ 2 := by omega
      have : 2 ^ 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2k
      omega
    have h8 : 8 ∣ 2 ^ 2 ^ k := by
      have : 2 ^ 3 ∣ 2 ^ 2 ^ k := pow_dvd_pow 2 h3
      simpa using this
    generalize 2 ^ 2 ^ k = t at hk h8
    omega
  · right
    have h4 : 4 ≤ k := by
      by_contra hlt
      have hk3 : k ≤ 3 := by omega
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    have h8 : 8 ∣ 2 ^ k := by
      have : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      simpa using this
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    exact ⟨by omega, k, by omega⟩

end Unc25K1

theorem l2pFacts : L2pFacts := by
  intro X _ _ hX
  rcases hX with ⟨p, hFM, h7, hmodel⟩ | hL32
  · have hp : p.Prime := hFM.1
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨K, _, _, _, e, hcard, -, -⟩ := K1.psl2_model_data (by omega) hmodel
    have hK : Nat.card K = p := by rw [Nat.card_eq_fintype_card, hcard, pow_one]
    exact Unc25K1.l2pData_of_mulEquiv e
      (Unc25K1.psl2_l2pData (by omega) hK (Unc25K1.fermat_or_mersenne_pow hFM h7))
  · obtain ⟨F, _, _, _, e, hq7, -, -⟩ := Unc25K1.exists_psl2_seven hL32
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have hK : Nat.card F = 7 := by rw [Nat.card_eq_fintype_card, hq7]
    exact Unc25K1.l2pData_of_mulEquiv e
      (Unc25K1.psl2_l2pData (p := 7) le_rfl hK (Or.inr ⟨by norm_num, 3, by norm_num⟩))

end CFSG.QuasithinUnique
