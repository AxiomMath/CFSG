module

public import CFSG.Foundations.Basic
import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

private theorem eq_one_of_sq_eq_one_of_odd {K : Type*} [Group K] (N : Subgroup K)
    (hN : Odd (Nat.card N)) {x : K} (hx : x ∈ N) (hx2 : x ^ 2 = 1) : x = 1 := by
  have hodd : Odd (orderOf x) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hx)
  rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx2) with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem pRank_two_eq_one_of_odd_cover {K L : Type} [Group K] [Finite K] [Group L] [Finite L]
    (f : K →* L) (hf : Function.Surjective f) (hk : Odd (Nat.card f.ker))
    (hL2 : Even (Nat.card L))
    (hinv : ∀ x y : L, orderOf x = 2 → orderOf y = 2 → x = y) : CFSG.pRank 2 K = 1 := by
  refine le_antisymm ?_ ?_
  · refine CFSG.LieType.SteinbergBR.pRank_le_of_card_le one_lt_two fun E hE => ?_
    have hsq : ∀ e ∈ E, e ^ 2 = 1 := fun e he =>
      CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) e he
    have hinj : Set.InjOn f (E : Set K) := by
      intro a ha b hb hab
      have hmem : a⁻¹ * b ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
      exact inv_mul_eq_one.1 (eq_one_of_sq_eq_one_of_odd _ hk hmem
        (hsq _ (E.mul_mem (E.inv_mem ha) hb)))
    have himg : ∀ e ∈ E, e ≠ 1 → orderOf (f e) = 2 := by
      intro e he he1
      refine orderOf_eq_prime (by rw [← map_pow, hsq e he, map_one]) fun h => he1 ?_
      exact hinj he E.one_mem (by rw [h, map_one])
    have hS : ((E : Set K) \ {1}).Subsingleton := fun a ha b hb =>
      hinj ha.1 hb.1 (hinv _ _ (himg a ha.1 ha.2) (himg b hb.1 hb.2))
    have h1 : ((E : Set K) \ {1}).ncard ≤ 1 := Set.ncard_le_one_iff_subsingleton.2 hS
    rw [Set.ncard_sdiff_singleton_of_mem (E.one_mem : (1 : K) ∈ (E : Set K))] at h1
    have h2 : Nat.card E = (E : Set K).ncard := Nat.card_coe_set_eq _
    omega
  · have h2 : 2 ∣ Nat.card K :=
      (even_iff_two_dvd.1 hL2).trans (Subgroup.card_dvd_of_surjective hf)
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
    have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
    have hE : CFSG.IsElementaryAbelian 2 (Subgroup.zpowers t) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one ht2
    have hcard : Nat.card (Subgroup.zpowers t) = 2 ^ 1 := by
      rw [Nat.card_zpowers, ht, pow_one]
    exact CFSG.LieType.SteinbergBR.le_pRank_of_card one_lt_two _ hE hcard

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
