module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cTop
public import CFSG.GH74.GLS.C3.Layer1.Thm1A7
public import CFSG.GH74.GLS.C3.Layer1.Ivk79Pump

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.E2
  CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1P31c CFSG.GH74.GLS.C3.Layer1.PumpCalc

namespace CFSG.GH74.GLS

theorem b_thm1_P31c_rel_proved
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hS34 : P34.S_prop34) (hGKF : GenericKnownFacts) (hE2 : E2ComponentFacts) :
    B_thm1_P31c_rel := by
  classical
  intro G _ _ hG hV x y K hu2 h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : orderOf x = 2 := hu2.1.1.1
  have hKC : K ≤ centralizer ({x} : Set G) := hu2.1.1.2.1
  have hxmem : x ∈ CxK x K := mem_CxK_self' hKC
  rcases lt_or_ge 2 (twoPartCard (CxK x K)) with hbig | hsmall
  swap
  ·
    refine isSylowOf_of_card (zpowers_le.2 hxmem) ?_
    rw [Nat.card_zpowers, hx2]
    have hdvd : 2 ∣ Nat.card ↥(CxK x K) := by
      have := orderOf_dvd_natCard (⟨x, hxmem⟩ : ↥(CxK x K))
      rwa [Subgroup.orderOf_mk, hx2] at this
    have hpos : 0 < Nat.card ↥(CxK x K) := Nat.card_pos
    have h1 : 1 ≤ (Nat.card ↥(CxK x K)).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos.ne').1 hdvd
    have hle : (Nat.card ↥(CxK x K)).factorization 2 ≤ 1 := by
      by_contra h
      push Not at h
      have h4 : 2 ^ 2 ≤ 2 ^ (Nat.card ↥(CxK x K)).factorization 2 :=
        Nat.pow_le_pow_right (by norm_num) h
      have hh : twoPartCard (CxK x K) = 2 ^ (Nat.card ↥(CxK x K)).factorization 2 := rfl
      omega
    have h2 : (Nat.card ↥(CxK x K)).factorization 2 = 1 := by omega
    rw [h2]
    norm_num
  · exfalso
    rcases Thm1.kBar_model_of_U2 hG h102 hL34 hu2 with hL2 | he7
    ·
      have hrk' : pRank 2 ↥(CxK x K) ≤ 1 :=
        Thm1P31c.pRank_le_one_of_card_le_two (Thm1.card_le_two_of_noV2Fine hV hu2 h5)
      have huniq := Thm1A7.unique_of_rank_le_one hGKF hE2 hL34 hG hrk' hu2
      obtain ⟨T, hT⟩ := Thm1.exists_setup1D x K
      obtain ⟨f, z, E⟩ := exists_env31 h2hb hG hV hu2 hL2 h5 huniq hT
      have hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K) := by
        rw [E.hQsyl.card_eq]
        exact hbig
      obtain ⟨f₁, b, p, D⟩ := E.exists_pump31data hG hS34 hQ3
      exact E.pump_false hGKF hE2 (Ivk79.c2Facts_of_facts hGKF hE2) hG hV h5 D
    ·
      rcases b_thm1_A7_any_proved hGKF hE2 hL34 hS34 G hG x y K hu2 he7 hbig with hrk | hexc
      · exact not_good_of_u2_not_five hV hu2 h5 (Or.inl hrk)
      · exact not_good_of_u2_not_five hV hu2 h5 (Or.inr hexc)

end CFSG.GH74.GLS
