module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRCert
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInner
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInvCentModelBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

theorem betaHat_pow {J : Subgroup G} {s : G} (hs : s ∈ normalizer (J : Set G))
    {q : Jhat J →* Equiv.Perm (Fin 42)} {r : Equiv.Perm (Fin 42)}
    (hr : ∀ e, q (betaHat J hs e) = r * q e * r⁻¹) (n : ℕ) (e : Jhat J) :
    q (betaHat J (pow_mem hs n) e) = r ^ n * q e * (r ^ n)⁻¹ := by
  induction n generalizing e with
  | zero =>
    rw [betaHat_eq_self J _ (pow_zero s)]
    simp
  | succ n ih =>
    rw [betaHat_congr J (pow_mem hs (n + 1)) (mul_mem (pow_mem hs n) hs) (pow_succ s n),
      betaHat_mul J (pow_mem hs n) hs, hr, ih, pow_succ']
    group

theorem outSquare :
    ∀ (G : Type) [Group G] [Finite G] (J : Subgroup G), ⁅J, J⁆ = J →
      IsL34Type (J ⧸ Open.fusionZStar J) → ∀ s ∈ normalizer (J : Set G),
        IsPGroup 2 ↥(zpowers s) → s * s ∈ withKernel J := by
  intro G _ _ J hJ hL s hs hs2
  obtain ⟨q, hqS, hqsurj, hqker, -⟩ := exists_jq hL
  obtain ⟨r, hrR, hr⟩ := exists_realization q hqS hqsurj (betaHat J hs) (fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e)
  obtain ⟨k, hk⟩ := hs2 ⟨s, mem_zpowers s⟩
  have hsk : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hrk : r ^ 2 ^ k = 1 := by
    have hc : r ^ 2 ^ k ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun t ht => ?_, pow_mem hrR _⟩
      obtain ⟨e, rfl⟩ := hqsurj t ht
      have h1 := betaHat_pow hs hr (2 ^ k) e
      rw [betaHat_eq_self J _ hsk] at h1
      calc q e * r ^ 2 ^ k = r ^ 2 ^ k * q e * (r ^ 2 ^ k)⁻¹ * r ^ 2 ^ k := by rw [← h1]
        _ = r ^ 2 ^ k * q e := by group
    rw [centralizer_S_inf_R] at hc
    exact mem_bot.mp hc
  have hr8 : r ^ 2 ^ 8 = 1 := by
    have hdvd : orderOf (⟨r, hrR⟩ : R) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hrk))
    obtain ⟨m, hm, hmo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hR : orderOf (⟨r, hrR⟩ : R) ∣ 241920 := card_R ▸ orderOf_dvd_natCard _
    rw [hmo] at hR
    have hm8 : m ≤ 8 := by
      by_contra h
      push Not at h
      have : 2 ^ 9 ∣ 241920 := (Nat.pow_dvd_pow 2 h).trans hR
      norm_num at this
    have h1 : (⟨r, hrR⟩ : R) ^ 2 ^ 8 = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (hmo ▸ Nat.pow_dvd_pow 2 hm8)
    have := congrArg Subtype.val h1
    simpa using this
  have hrr := sq_mem_S_of_pow_two hrR hr8
  obtain ⟨e₀, he₀⟩ := hqsurj _ hrr
  refine mem_withKernel_of_realization hJ (mul_mem hs hs) hqker (e₀ := e₀) fun e => ?_
  rw [betaHat_mul J hs hs, hr, hr, he₀]
  group

end CFSG.ComponentClassification.GrSLit.L34Facts
