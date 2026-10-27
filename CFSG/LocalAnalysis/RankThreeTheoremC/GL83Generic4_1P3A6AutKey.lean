module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

private theorem center_eq_bot_of_simple {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hK : Nat.card K = 360) {Q : Subgroup K} (hQ : Nat.card Q = 9) : center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
  · exact h
  · exfalso
    have hc : ∀ g k : K, g * k = k * g := fun g k =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top k) g
    have : Q.Normal := ⟨fun n hn g => by rw [hc g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Q with h' | h'
    · rw [h', Subgroup.card_bot] at hQ
      omega
    · rw [h', Subgroup.card_top, hK] at hQ
      omega

private theorem conj_injective_of_center_eq_bot {K : Type} [Group K] (h : center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have : k ∈ center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut K => φ g) hk
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * k = (k * g * k⁻¹) * k := by rw [h1]
      _ = k * g := by group
  rw [h, Subgroup.mem_bot] at this
  exact this

private theorem normal_range_conj {K : Type} [Group K] :
    ((MulAut.conj : K →* MulAut K).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  refine ⟨g k, ?_⟩
  ext x
  simp [MulAut.conj_apply]

private theorem exists_conj_of_orderOf_five {K : Type} [Group K] [Finite (MulAut K)]
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) (hK : Nat.card K = 360)
    (hcard : Nat.card (MulAut K) = 1440) {ψ : MulAut K} (hψ : orderOf ψ = 5) :
    ∃ k : K, MulAut.conj k = ψ := by
  have : ((MulAut.conj : K →* MulAut K).range).Normal := normal_range_conj
  set Inn : Subgroup (MulAut K) := (MulAut.conj : K →* MulAut K).range with hInn
  have hInnCard : Nat.card Inn = 360 := by
    rw [← hK]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hidx : Inn.index = 4 := by
    have h := Inn.index_mul_card
    rw [hInnCard, hcard] at h
    omega
  have h4 : orderOf (QuotientGroup.mk ψ : MulAut K ⧸ Inn) ∣ 4 := by
    rw [← hidx, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h5 : orderOf (QuotientGroup.mk ψ : MulAut K ⧸ Inn) ∣ 5 := by
    rw [← hψ]
    exact orderOf_map_dvd (QuotientGroup.mk' Inn) ψ
  have h1 : orderOf (QuotientGroup.mk ψ : MulAut K ⧸ Inn) = 1 :=
    Nat.dvd_one.mp (by simpa using Nat.dvd_gcd h4 h5)
  exact (QuotientGroup.eq_one_iff ψ).mp (orderOf_eq_one_iff.mp h1)

theorem aut_eq_one_of_commute {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    [Finite (MulAut K)] (hK : Nat.card K = 360) (hcard : Nat.card (MulAut K) = 1440)
    (hcent : ∀ R : Subgroup (MulAut K), (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) → (∀ a ∈ R, a ^ 3 = 1) →
      Nat.card R = 9 → ∀ ψ : MulAut K, ψ ^ 2 = 1 → (∀ r ∈ R, ψ * r = r * ψ) → ψ = 1)
    (hcent3 : ∀ B : Subgroup K, (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ a ∈ B, a ^ 3 = 1) →
      Nat.card B = 9 → ∀ k : K, (∀ b ∈ B, k * b = b * k) → k ∈ B)
    {Q : Subgroup K} (hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hQ3 : ∀ a ∈ Q, a ^ 3 = 1)
    (hQn : Nat.card Q = 9) (ψ : MulAut K) (hψ : Nat.Coprime 3 (orderOf ψ))
    (hcomm : ∀ t ∈ Q, ψ * MulAut.conj t = MulAut.conj t * ψ) : ψ = 1 := by
  have hinj := conj_injective_of_center_eq_bot (center_eq_bot_of_simple hK hQn)
  by_contra hne
  have ho1 : orderOf ψ ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd ho1
  have hdvd : orderOf ψ ∣ 1440 := hcard ▸ orderOf_dvd_natCard ψ
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    exact absurd (Nat.Coprime.eq_one_of_dvd hψ hℓd) (by norm_num)
  have hℓ25 : ℓ = 2 ∨ ℓ = 5 := by
    have h : ℓ ∣ 2 ^ 5 * 3 ^ 2 * 5 := by
      norm_num
      exact hℓd.trans hdvd
    rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h))
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp
          (hℓ.dvd_of_dvd_pow h)) hℓ3
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).mp h)
  set ψ' : MulAut K := ψ ^ (orderOf ψ / ℓ) with hψ'
  have hord : orderOf ψ' = ℓ := orderOf_pow_orderOf_div (orderOf_pos ψ).ne' hℓd
  have hcomm' : ∀ t ∈ Q, ψ' * MulAut.conj t = MulAut.conj t * ψ' := fun t ht =>
    (Commute.pow_left (show Commute ψ (MulAut.conj t) from hcomm t ht) _).eq
  rcases hℓ25 with rfl | rfl
  · have hψ'2 : ψ' ^ 2 = 1 := by
      have := pow_orderOf_eq_one ψ'
      rwa [hord] at this
    have h1 : ψ' = 1 := by
      refine hcent (Q.map (MulAut.conj : K →* MulAut K)) ?_ ?_ ?_ ψ' hψ'2 ?_
      · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
        rw [← map_mul, ← map_mul, hQc s hs t ht]
      · rintro _ ⟨s, hs, rfl⟩
        rw [← map_pow, hQ3 s hs, map_one]
      · rw [Subgroup.card_map_of_injective hinj]
        exact hQn
      · rintro _ ⟨t, ht, rfl⟩
        exact hcomm' t ht
    rw [h1, orderOf_one] at hord
    omega
  · obtain ⟨k, hk⟩ := exists_conj_of_orderOf_five hinj hK hcard hord
    have hkc : ∀ b ∈ Q, k * b = b * k := by
      intro b hb
      apply hinj
      rw [map_mul, map_mul, hk]
      exact hcomm' b hb
    have hkQ : k ∈ Q := hcent3 Q hQc hQ3 hQn k hkc
    have h3 : ψ' ^ 3 = 1 := by rw [← hk, ← map_pow, hQ3 k hkQ, map_one]
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hord] at this
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC
