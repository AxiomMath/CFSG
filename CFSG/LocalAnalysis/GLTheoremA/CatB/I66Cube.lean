module

public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Subgroup

theorem i66_zpowers_normal {K : Type} [Group K] {x : K} (hx : x ∈ Subgroup.center K) :
    (Subgroup.zpowers x).Normal where
  conj_mem n hn g := by
    have hc : n ∈ Subgroup.center K := (Subgroup.zpowers_le.mpr hx) hn
    have hcomm := Subgroup.mem_center_iff.mp hc g
    rw [hcomm, mul_inv_cancel_right]
    exact hn

theorem i66_pow_three_of_mem_center {K : Type} [Group K] (hn : Nat.card (Subgroup.center K) = 3)
    {c : K} (hc : c ∈ Subgroup.center K) : c ^ 3 = 1 := by
  have h1 : (⟨c, hc⟩ : Subgroup.center K) ^ 3 = 1 := by
    have h2 := pow_card_eq_one' (G := Subgroup.center K) (x := ⟨c, hc⟩)
    rwa [hn] at h2
  simpa using congrArg Subtype.val h1

theorem i66_card_center_eq_three {K : Type} [Group K] [Finite K]
    (hO : CFSG.Open.GLAPPrimeCore 3 K = ⊥) {z : K} (hz : z ∈ Subgroup.center K)
    (hzo : orderOf z = 3) {m : ℕ} (hd : Nat.card (Subgroup.center K) ∣ m) (h9 : ¬ 9 ∣ m) :
    Nat.card (Subgroup.center K) = 3 := by
  have hO' : CFSG.pPrimeCore 3 K = ⊥ := hO
  have hprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card (Subgroup.center K) → q = 3 := by
    intro q hq hqd
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) q hqd
    by_contra hq3
    have hxo : orderOf (x : K) = q := by rw [Subgroup.orderOf_coe]; exact hx
    have hNle : Subgroup.zpowers (x : K) ≤ CFSG.pPrimeCore 3 K := by
      apply le_sSup
      refine ⟨i66_zpowers_normal x.2, ?_⟩
      rw [Nat.card_zpowers, hxo]
      exact (Nat.coprime_primes Nat.prime_three hq).2 (Ne.symm hq3)
    rw [hO'] at hNle
    have h1 : (x : K) ∈ (⊥ : Subgroup K) := Subgroup.zpowers_le.mp hNle
    rw [Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hxo
    exact hq.one_lt.ne hxo
  have h3 : 3 ∣ Nat.card (Subgroup.center K) := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center K) hz
    rwa [hzo] at h
  have hpow : Nat.card (Subgroup.center K) = 3 ^ (Nat.card (Subgroup.center K)).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos).ne' (fun hd' hdd => hprime _ hd' hdd)
  obtain ⟨k, hk⟩ : ∃ k, Nat.card (Subgroup.center K) = 3 ^ k := ⟨_, hpow⟩
  rw [hk] at h3 hd ⊢
  rcases k with _ | _ | k
  · norm_num at h3
  · norm_num
  · exfalso
    apply h9
    have h2 : 3 ^ 2 ∣ m := (pow_dvd_pow 3 (show 2 ≤ k + 1 + 1 by omega)).trans hd
    norm_num at h2
    exact h2

theorem i66_cube_false {K Y : Type} [Group K] [Finite K] [Group Y] {z : K}
    (hz : z ∈ Subgroup.center K) (hzo : orderOf z = 3) (hn : Nat.card (Subgroup.center K) = 3)
    (e : K ⧸ Subgroup.center K ≃* Y) (hY : ∀ t : Y, orderOf t = 3 → IsConj t t⁻¹) (g : K)
    (hg : g ^ 3 = z) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht3 : (QuotientGroup.mk g : K ⧸ Subgroup.center K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hg]
    exact (QuotientGroup.eq_one_iff z).mpr hz
  by_cases ht1 : (QuotientGroup.mk g : K ⧸ Subgroup.center K) = 1
  ·
    have hgc : g ∈ Subgroup.center K := (QuotientGroup.eq_one_iff g).mp ht1
    have h1 := i66_pow_three_of_mem_center hn hgc
    rw [hg] at h1
    rw [h1, orderOf_one] at hzo
    norm_num at hzo
  · have hto : orderOf (QuotientGroup.mk g : K ⧸ Subgroup.center K) = 3 :=
      orderOf_eq_prime ht3 ht1
    have hyo : orderOf (e (QuotientGroup.mk g : K ⧸ Subgroup.center K)) = 3 := by
      rw [MulEquiv.orderOf_eq]
      exact hto
    obtain ⟨c, hc⟩ := isConj_iff.mp (hY _ hyo)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm c)
    have hinv : e.symm c * (QuotientGroup.mk g : K ⧸ Subgroup.center K) * (e.symm c)⁻¹ =
        (QuotientGroup.mk g : K ⧸ Subgroup.center K)⁻¹ := by
      have key := congrArg e.symm hc
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply] at key
      exact key
    have hmk : (QuotientGroup.mk (k * g * k⁻¹) : K ⧸ Subgroup.center K) =
        QuotientGroup.mk g⁻¹ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hk, hinv,
        QuotientGroup.mk_inv]
    have hcen : (g⁻¹)⁻¹ * (k * g * k⁻¹) ∈ Subgroup.center K := QuotientGroup.eq.mp hmk.symm
    obtain ⟨c', hc'⟩ : ∃ c', c' = (g⁻¹)⁻¹ * (k * g * k⁻¹) := ⟨_, rfl⟩
    rw [← hc'] at hcen
    have hkey : k * g * k⁻¹ = g⁻¹ * c' := by
      rw [hc']
      group
    have hcomm : Commute g⁻¹ c' := Subgroup.mem_center_iff.mp hcen g⁻¹
    have h1 : (k * g * k⁻¹) ^ 3 = z := by
      rw [conj_pow, hg, (Subgroup.mem_center_iff.mp hz k)]
      group
    have h2 : (k * g * k⁻¹) ^ 3 = z⁻¹ := by
      rw [hkey, hcomm.mul_pow, inv_pow, hg, i66_pow_three_of_mem_center hn hcen, mul_one]
    have hz1 : z = z⁻¹ := h1.symm.trans h2
    have hz2 : z ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hz1]
      exact mul_inv_cancel z
    have h4 := orderOf_dvd_of_pow_eq_one hz2
    rw [hzo] at h4
    norm_num at h4

theorem i66_center_eq_bot {K : Type} [Group K] (p : ℕ)
    (hO : CFSG.Open.GLAPPrimeCore p K = ⊥) (hp : Nat.Coprime p (Nat.card (Subgroup.center K))) :
    Subgroup.center K = ⊥ := by
  have hO' : CFSG.pPrimeCore p K = ⊥ := hO
  have hle : Subgroup.center K ≤ CFSG.pPrimeCore p K := le_sSup ⟨inferInstance, hp⟩
  rw [hO'] at hle
  exact le_bot_iff.mp hle

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
