module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Model
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

private theorem l28m_no_order_nine {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 7) (σ : Equiv.Perm Ω) : orderOf σ ≠ 9 := by
  intro h
  have hl := Equiv.Perm.lcm_cycleType σ
  rw [h] at hl
  have hdvd : σ.cycleType.lcm ∣ 3 := by
    refine Multiset.lcm_dvd.mpr fun n hn => ?_
    have h1 : n ∣ 9 := hl ▸ Multiset.dvd_lcm hn
    have h2 : n ≤ 7 := by
      have := Equiv.Perm.sum_cycleType σ
      have h3 : n ≤ σ.cycleType.sum := Multiset.le_sum_of_mem hn
      have h4 : σ.support.card ≤ Fintype.card Ω := Finset.card_le_univ _
      omega
    have h5 : n ∈ ({1, 3, 9} : Finset ℕ) := by
      have : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [← this]
      exact Nat.mem_divisors.mpr ⟨h1, by norm_num⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at h5
    rcases h5 with rfl | rfl | rfl
    · exact one_dvd _
    · exact dvd_rfl
    · omega
  rw [hl] at hdvd
  omega

private theorem l28m_no_small_index {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hK : Nat.card K = 504) {c : K} (hc : orderOf c = 9) {Y : Subgroup K}
    (hY : Y.index = 4 ∨ Y.index = 7) : False := by
  have hYtop : Y ≠ ⊤ := by
    rintro rfl
    simp at hY
  have hcore : Y.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ Y.normalCore_le)) hYtop
  have hinj : Function.Injective (MulAction.toPermHom K (K ⧸ Y)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
    exact hcore
  have hΩ : Nat.card (K ⧸ Y) = Y.index := (Subgroup.index_eq_card Y).symm
  rcases hY with h4 | h7
  · have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm, hΩ, h4, hK] at h1
    norm_num [Nat.factorial] at h1
  · have : Fintype (K ⧸ Y) := Fintype.ofFinite _
    have hcard : Fintype.card (K ⧸ Y) = 7 := by
      rw [← Nat.card_eq_fintype_card, hΩ, h7]
    classical
    exact l28m_no_order_nine hcard (MulAction.toPermHom K (K ⧸ Y) c)
      (by rw [orderOf_injective _ hinj c, hc])

private theorem l28m_index_cases {n : ℕ} (hd : n ∣ 56) (hm : n ≡ 1 [MOD 3]) :
    n = 1 ∨ n = 4 ∨ n = 7 ∨ n = 28 := by
  have hle : n ≤ 56 := Nat.le_of_dvd (by norm_num) hd
  have hm' : n % 3 = 1 := hm
  interval_cases n <;> omega

private theorem l28m_factor_cases {m d : ℕ} (hmd : m * d = 28) (hm : m ≡ 1 [MOD 3]) :
    (m = 1 ∧ d = 28) ∨ (m = 4 ∧ d = 7) ∨ (m = 7 ∧ d = 4) ∨ (m = 28 ∧ d = 1) := by
  have hdvd : m ∣ 28 := ⟨d, hmd.symm⟩
  have hle : m ≤ 28 := Nat.le_of_dvd (by norm_num) hdvd
  have hm' : m % 3 = 1 := hm
  interval_cases m <;> omega

theorem l28m_card_sylow {K : Type} [Group K] [Finite K] (hK : IsRankThreeL28 K) (T : Sylow 3 K) :
    Nat.card (T : Subgroup K) = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : (504 : ℕ).factorization 3 = 2 := by decide +kernel
  rw [T.card_eq_multiplicity, l28m_card hK, h]

theorem l28m_index_normalizer {K : Type} [Group K] [Finite K] (hK : IsRankThreeL28 K)
    (T : Sylow 3 K) : (normalizer ((T : Subgroup K) : Set K)).index = 28 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup K := l28m_simple hK
  obtain ⟨c, hc⟩ := l28m_exists_order_nine hK
  have hcard := l28m_card hK
  have hT := l28m_card_sylow hK T
  set N := normalizer ((T : Subgroup K) : Set K) with hN
  have h9 : 9 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le (le_normalizer (H := (T : Subgroup K)))
    rwa [hT] at this
  have hmul : N.index * Nat.card N = 504 := by rw [N.index_mul_card, hcard]
  have hmod : N.index ≡ 1 [MOD 3] := by
    have h := card_sylow_modEq_one 3 K
    rwa [T.card_eq_index_normalizer] at h
  have hdvd : N.index ∣ 56 := by
    obtain ⟨k, hk⟩ := h9
    have h56 : N.index * k = 56 := by
      have : 9 * (N.index * k) = 9 * 56 := by
        calc 9 * (N.index * k) = N.index * (9 * k) := by ring
          _ = 504 := by rw [← hk]; exact hmul
          _ = 9 * 56 := by norm_num
      omega
    exact ⟨k, h56.symm⟩
  rcases l28m_index_cases hdvd hmod with h1 | h4 | h7 | h28
  · exfalso
    have hnorm : (T : Subgroup K).Normal :=
      normalizer_eq_top_iff.mp (index_eq_one.mp h1)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T : Subgroup K) with h | h
    · rw [h, Subgroup.card_bot] at hT
      omega
    · rw [h, Subgroup.card_top, hcard] at hT
      omega
  · exact (l28m_no_small_index hcard hc (Or.inl h4)).elim
  · exact (l28m_no_small_index hcard hc (Or.inr h7)).elim
  · exact h28

theorem l28m_card_normalizer {K : Type} [Group K] [Finite K] (hK : IsRankThreeL28 K)
    (T : Sylow 3 K) : Nat.card (normalizer ((T : Subgroup K) : Set K)) = 18 := by
  have h := (normalizer ((T : Subgroup K) : Set K)).index_mul_card
  rw [l28m_index_normalizer hK T, l28m_card hK] at h
  omega

theorem l28m_centralizer_sylow {K : Type} [Group K] [Finite K] (hK : IsRankThreeL28 K)
    (T : Sylow 3 K) : centralizer ((T : Subgroup K) : Set K) ≤ (T : Subgroup K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT := l28m_card_sylow hK T
  have hN := l28m_card_normalizer hK T
  set N := normalizer ((T : Subgroup K) : Set K) with hNdef
  set C := centralizer ((T : Subgroup K) : Set K) with hCdef
  have hcomm : IsMulCommutative (T : Subgroup K) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hT
  have hTC : (T : Subgroup K) ≤ C := Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm
  have hCN : C ≤ N := centralizer_le_normalizer _
  have hdvd9 : 9 ∣ Nat.card C := by
    have := Subgroup.card_dvd_of_le hTC
    rwa [hT] at this
  have hle : Nat.card C ≤ 18 := by
    rw [← hN]
    exact Subgroup.card_le_of_le hCN
  obtain ⟨k, hk⟩ := hdvd9
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hk' : k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl
  · exact (Subgroup.eq_of_le_of_card_ge hTC (by rw [hT, hk]; norm_num)).symm.le
  · exfalso
    have hCeq : C = N := Subgroup.eq_of_le_of_card_ge hCN (by rw [hN, hk])
    obtain ⟨t₁, ht₁⟩ := exists_prime_orderOf_dvd_card' (G := (T : Subgroup K)) 3
      (by rw [hT]; exact dvd_pow_self 3 two_ne_zero)
    obtain ⟨m, hmN, -, hm⟩ := l28m_sylow_inv hK T
    have ht₁T : (t₁ : K) ∈ (T : Subgroup K) := t₁.2
    have ht₁ord : orderOf (t₁ : K) = 3 := by rw [Subgroup.orderOf_coe]; exact ht₁
    have hmC : m ∈ C := hCeq ▸ hmN
    have hcm : (t₁ : K) * m = m * t₁ := mem_centralizer_iff.mp hmC _ ht₁T
    have h1 : m * t₁ * m⁻¹ = (t₁ : K) := by rw [← hcm]; group
    have h2 : (t₁ : K) = (t₁ : K)⁻¹ := h1.symm.trans (hm _ ht₁T)
    have h3 : orderOf (t₁ : K) ∣ 2 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr h2
    rw [ht₁ord] at h3
    omega

theorem l28Three_proved : KFactL28Three := by
  intro K _ _ hK T
  refine ⟨l28m_card_sylow hK T, fun Y hY => ?_⟩
  have : IsSimpleGroup K := l28m_simple hK
  obtain ⟨c, hc⟩ := l28m_exists_order_nine hK
  have hmul := index_normalizer_eq_mul (T := (T : Subgroup K)) hY
  have hmod := relIndex_normalizer_modEq_one T hY
  rw [l28m_index_normalizer hK T] at hmul
  rcases l28m_factor_cases hmul.symm hmod with ⟨h1, -⟩ | ⟨-, h7⟩ | ⟨-, h4⟩ | ⟨-, h1⟩
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp h1) hY)
  · exact (l28m_no_small_index (l28m_card hK) hc (Or.inr h7)).elim
  · exact (l28m_no_small_index (l28m_card hK) hc (Or.inl h4)).elim
  · exact Or.inr (index_eq_one.mp h1)

end CFSG.LocalAnalysis.RankThreeTheoremC
