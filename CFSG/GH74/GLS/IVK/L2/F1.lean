module

public import CFSG.GH74.GLS.IVK.L2.FixedCentralizer
public import CFSG.GH74.GLS.IVK.L2.Lemma12i

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup

theorem not_two_pow_succ_dvd (q₀ : ℕ) (hq₀ : Odd q₀) (hq₀3 : 3 ≤ q₀) (n : ℕ)
    (hn : n = (q₀ ^ 2 * ((q₀ ^ 2) ^ 2 - 1) / 2).factorization 2) :
    ¬ 2 ^ (n + 1) ∣ q₀ * (q₀ ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := hq₀
  obtain ⟨t, ht⟩ : ∃ t, q₀ ^ 2 = 8 * t + 1 := by
    rcases Nat.even_or_odd s with ⟨u, hu⟩ | ⟨u, hu⟩
    · exact ⟨u * (2 * u + 1), by subst hs; subst hu; ring⟩
    · exact ⟨(2 * u + 1) * (u + 1), by subst hs; subst hu; ring⟩
  have htpos : 0 < t := by
    by_contra h0
    have : t = 0 := by omega
    subst this
    have : q₀ ≤ 1 := by nlinarith
    omega
  have hX : q₀ ^ 2 - 1 = 8 * t := by omega
  have hK : q₀ ^ 2 * ((q₀ ^ 2) ^ 2 - 1) / 2 = q₀ ^ 2 * (8 * t) * (4 * t + 1) := by
    rw [ht]
    have : (8 * t + 1) * ((8 * t + 1) ^ 2 - 1) = 2 * ((8 * t + 1) * (8 * t) * (4 * t + 1)) := by
      have h1 : (8 * t + 1) ^ 2 - 1 = 8 * t * (8 * t + 2) := by
        have : (8 * t + 1) ^ 2 = 8 * t * (8 * t + 2) + 1 := by ring
        omega
      rw [h1]; ring
    rw [this]
    omega
  have hq2odd : ¬ 2 ∣ q₀ ^ 2 := by
    intro h2
    have : 2 ∣ q₀ := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)
    omega
  have h4t : ¬ 2 ∣ 4 * t + 1 := by omega
  have hv : n = padicValNat 2 (8 * t) := by
    rw [hn, hK, Nat.factorization_def _ Nat.prime_two]
    rw [padicValNat.mul (by positivity) (by omega), padicValNat.mul (by positivity) (by omega)]
    rw [padicValNat.eq_zero_of_not_dvd hq2odd, padicValNat.eq_zero_of_not_dvd h4t]
    simp
  intro hdvd
  have hcop : Nat.Coprime (2 ^ (n + 1)) q₀ := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    exact ⟨s, hs⟩
  rw [hX] at hdvd
  have h8 : 2 ^ (n + 1) ∣ 8 * t := hcop.dvd_of_dvd_mul_left hdvd
  have h9 := (padicValNat_dvd_iff_le (p := 2) (a := 8 * t) (n := n + 1) (by omega)).mp h8
  omega

theorem fInvNotCentPt : FInvNotCentPt := by
  intro F _ _ hF K _ _ e N f hf hf2 hcomm
  obtain ⟨σ, rfl⟩ : f ∈ fieldAutSub e := hf.2
  have hσ2 : orderOf σ = 2 := by
    rw [← orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) σ]
    exact hf2
  have hq : Nat.card (fixedField σ) ^ 2 = Nat.card F := by
    have := fixedField_card_pow σ
    rwa [hσ2] at this
  have hodd : Odd (Nat.card (fixedField σ)) := odd_card_fixedField σ hF.1
  have h3 : 3 ≤ Nat.card (fixedField σ) := by
    have h1 := one_lt_card_fixedField σ
    obtain ⟨s, hs⟩ := hodd
    omega
  have hcard := card_centralizer_fieldAut e σ
  have hle : N.Pt ≤ centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e := by
    intro d hd
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, hd.2⟩
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (hcomm d hd).symm
  have hdvd : Nat.card N.Pt ∣ Nat.card (fixedField σ) * (Nat.card (fixedField σ) ^ 2 - 1) := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hle
  have hPt : Nat.card N.Pt = 2 ^ ((Nat.card K).factorization 2 + 1) := by
    rw [card_Pt_eq hF N, card_P_eq e N, pow_succ]
    ring
  have hK : Nat.card K = Nat.card (fixedField σ) ^ 2 *
      ((Nat.card (fixedField σ) ^ 2) ^ 2 - 1) / 2 := by
    rw [card_eq_of_L2Field e hF, hq]
  rw [hPt] at hdvd
  apply not_two_pow_succ_dvd (Nat.card (fixedField σ)) hodd h3 ((Nat.card K).factorization 2)
  · rw [hK]
  · exact hdvd

theorem ivk_1_2i_a : IVK_1_2i_a := ivk_1_2i_a_of fInvNotCentPt

theorem ivk_1_2i_c : IVK_1_2i_c := ivk_1_2i_c_of fInvNotCentPt

end CFSG.GH74.GLS.IVK
