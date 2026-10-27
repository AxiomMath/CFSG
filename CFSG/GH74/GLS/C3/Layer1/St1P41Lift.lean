module

public import CFSG.GH74.GLS.C3.Layer1.St1Iv251

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpLift

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_involutions_mod_odd {M : Subgroup G} {a b : G} (_ha : a ∈ M) (_hb : b ∈ M)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a⁻¹ * b ∈ pPrimeCoreOf 2 M) :
    ∃ o ∈ pPrimeCoreOf 2 M, o * a * o⁻¹ = b := by
  set c := a⁻¹ * b with hc
  have ha' : a ^ 2 = 1 := by rw [← ha2]; exact pow_orderOf_eq_one a
  have hb' : b ^ 2 = 1 := by rw [← hb2]; exact pow_orderOf_eq_one b
  have hainv : a⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one, ← sq]
    exact ha'
  have hbc : b = a * c := by rw [hc, mul_inv_cancel_left]
  have hconj : a * c * a⁻¹ = c⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    have h1 : (a * c) * (a * c) = 1 := by rw [← hbc, ← sq]; exact hb'
    calc a * c * a⁻¹ * c = (a * c) * (a * c) := by rw [hainv]; group
      _ = 1 := h1
  have hodd : Odd (orderOf c) := by
    have hdvd : orderOf c ∣ Nat.card (pPrimeCoreOf 2 M) := by
      have := orderOf_dvd_natCard (⟨c, hab⟩ : pPrimeCoreOf 2 M)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd M) hdvd
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * m = orderOf c + 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  set s := c ^ m with hs
  have hss : s * s = c := by
    rw [hs, ← pow_add, ← two_mul, hm, pow_succ, pow_orderOf_eq_one, one_mul]
  have has : a * s * a⁻¹ = s⁻¹ := by
    rw [hs, ← conj_pow, hconj, inv_pow]
  have has' : a * s = s⁻¹ * a := by
    rw [← has]
    group
  refine ⟨s⁻¹, inv_mem (pow_mem hab m), ?_⟩
  rw [inv_inv, hbc, ← hss]
  calc s⁻¹ * a * s = (s⁻¹ * a) * s := rfl
    _ = a * s * s := by rw [← has']
    _ = a * (s * s) := by rw [mul_assoc]

theorem exists_involution_central {K P : Subgroup G} (hP : IsPGroup 2 ↥P)
    (hPK : P ≤ normalizer (K : Set G)) (hK : 2 ∣ Nat.card ↥K) :
    ∃ z ∈ K, orderOf z = 2 ∧ ∀ p ∈ P, z * p = p * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, -, hPQ⟩ := Iv251.exists_invariant_sylow (C := K) (Q := ⊥) (V := P) bot_le
    (IsPGroup.of_card (n := 0) (by simp)) hP hPK
    (fun p _ => by rw [Subgroup.normalizer_eq_top]; trivial)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    have h1 := hQ.card_eq
    rw [h, Subgroup.card_bot] at h1
    have h2 : 1 ≤ (Nat.card K).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two (Nat.card_pos).ne').mp hK
    have h3 : 2 ≤ 2 ^ (Nat.card K).factorization 2 := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hQP : IsPGroup 2 ↥(Q ⊔ P) := hQ.isPGroup.to_sup_of_normal_left' hP hPQ
  obtain ⟨z, hzQ, hz2, hzc⟩ := Iv251.exists_central_involution hQP le_sup_left
    (sup_le Subgroup.le_normalizer hPQ) hQ0
  exact ⟨z, hQ.le hzQ, hz2, fun p hp => hzc p ((le_sup_right : P ≤ Q ⊔ P) hp)⟩

theorem exists_isElementaryAbelian_card_pRank {H : Type*} [Group H] [Finite H] :
    ∃ A : Subgroup H, IsElementaryAbelian 2 ↥A ∧ Nat.card A = 2 ^ pRank 2 H := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (G := H) one_lt_two ⊤
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact ⟨E, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mpr hE, hcard⟩

end CFSG.GH74.GLS.C3.Layer1.PumpLift
