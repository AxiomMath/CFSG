module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeRoot

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

theorem prime_one_add_nCount (ε : Eps) : (1 + nCount ε).Prime := by
  cases ε <;> norm_num [nCount]

theorem not_modEq_one_add_nCount (ε : Eps) :
    ∀ d, d < 128 → d ∣ 128 → ¬ 128 ≡ d [MOD 1 + nCount ε] := by
  cases ε <;> decide

theorem exists_add_zero (ε : Eps) (v : V6) :
    ∃ s : V6, qfV ε s = 0 ∧ qfV ε (v + s) = 0 := by
  have h := (cprimeChecks ε).2.2.2.2
  simp only [sumCheck, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨s, hs, hs1, hs2⟩ := h (vecBits v) (vecBits_lt v)
  refine ⟨toVec 6 s, ?_, ?_⟩
  · rw [qfV_toVec ε hs, hs1, bz_false]
  · have hlt : vecBits v ^^^ s < 64 := Nat.xor_lt_two_pow (n := 6) (vecBits_lt v) hs
    rw [← toVec_vecBits v, ← toVec_xor, qfV_toVec ε hlt, hs2, bz_false]

theorem ne_zero_of_qfV_eq_one {ε : Eps} {u : V6} (hu : qfV ε u = 1) : u ≠ 0 := fun h => by
  rw [h, qfV_zero] at hu; exact zero_ne_one hu

namespace Setting

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G} {c : G}
  {v₀ : ℕ} (hS : Setting ε t L U Q P a ψ p c v₀)
include hS

theorem false_of_Zset_nonsing [Finite G] (hZ : ∀ v, v ∈ Zset t Q ψ ↔ v = 0 ∨ qfV ε v = 1) :
    False := by
  classical
  set E : Subgroup G := Q ⊔ zpowers t
  have hcardZ : Nat.card (Zset t Q ψ) = 1 + nCount ε := by
    have hset : Zset t Q ψ =
        ↑(insert (0 : V6) (Finset.univ.filter fun v : V6 => qfV ε v = 1)) := by
      ext v
      simp only [hZ, Finset.coe_insert, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_insert_iff, Set.mem_ofPred_eq]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_insert_of_notMem (by
      simp [qfV_zero]), card_qfV_one, add_comm]
  have hq := prime_one_add_nCount ε
  have hdvd : 1 + nCount ε ∣ Nat.card (normalizer (E : Set G)) := by
    rw [hS.card_normalizer_E, hcardZ]
    exact dvd_mul_right _ _
  have : Fact (1 + nCount ε).Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (E : Set G)) _ hdvd
  have hx' : orderOf (x : G) = 1 + nCount ε := by rwa [Subgroup.orderOf_coe]
  obtain ⟨d, hd1, hd2, hd3⟩ := exists_dvd_modEq_of_orderOf hS.card_E hS.centralizer_E_le x.2 hq
    hx' (by cases ε <;> norm_num [nCount])
  exact not_modEq_one_add_nCount ε d hd2 hd1 hd3

theorem conj_ψ_mem_Q (hZ : ∀ s, qfV ε s = 0 → s ∈ Zset t Q ψ)
    {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    g * ψ v * g⁻¹ ∈ Q := by
  have hsing : ∀ s, qfV ε s = 0 → g * ψ s * g⁻¹ ∈ Q := by
    intro s hs
    obtain ⟨k, hk, hks⟩ := hZ s hs
    obtain ⟨w₁, hw₁⟩ := hS.conj_t_eq hg
    obtain ⟨w₂, hw₂⟩ := hS.conj_t_eq (mul_mem hg hk)
    have e1 : g * t * g⁻¹ * (g * k * t * (g * k)⁻¹) = g * (t * (k * t * k⁻¹)) * g⁻¹ := by group
    rw [hks, ← mul_assoc t t, hS.shape.mul_self, one_mul, hw₁, hw₂, hS.tψ_mul_tψ] at e1
    rw [← e1]
    exact hS.rad.ψ_mem _
  obtain ⟨s, hs1, hs2⟩ := exists_add_zero ε v
  have hv : ψ v = ψ s * ψ (v + s) := by
    rw [← hS.rad.ψ_add]
    congr 1
    rw [add_comm v s, ← add_assoc, add_self_V6, zero_add]
  rw [hv, show g * (ψ s * ψ (v + s)) * g⁻¹ = (g * ψ s * g⁻¹) * (g * ψ (v + s) * g⁻¹) by group]
  exact mul_mem (hsing s hs1) (hsing _ hs2)

theorem normalizer_E_le_Q
    (hZ : ∀ s, qfV ε s = 0 → s ∈ Zset t Q ψ) :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (Q : Set G) := by
  intro g hg
  refine mem_normalizer_iff.2 fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  · obtain ⟨v, rfl⟩ := hS.rad.mem_ψ n hn
    exact hS.conj_ψ_mem_Q hZ hg v
  · obtain ⟨v, hv⟩ := hS.rad.mem_ψ _ hn
    have h := hS.conj_ψ_mem_Q hZ (inv_mem hg) v
    rw [hv, inv_inv, show g⁻¹ * (g * n * g⁻¹) * g = n by group] at h
    exact h

theorem Kgrp_eq (hZ : ∀ s, qfV ε s = 0 → s ∈ Zset t Q ψ) :
    Kgrp t Q = normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  inf_of_le_left (hS.normalizer_E_le_Q hZ)

theorem le_card_range [Finite G]
    (hZ : ∀ s, qfV ε s = 0 → s ∈ Zset t Q ψ) :
    Nat.card (Zset t Q ψ) * oBound ε ≤ Nat.card hS.affHom.range := by
  have h1 := hS.card_range_mul
  have h2 : Nat.card (Kgrp t Q) =
      Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) := by
    rw [hS.Kgrp_eq hZ]
  obtain ⟨b, hb⟩ : ∃ b, oBound ε = 2 * b := ⟨oBound ε / 2, by cases ε <;> rfl⟩
  refine Nat.le_of_mul_le_mul_right ?_ (show 0 < 128 by norm_num)
  calc Nat.card (Zset t Q ψ) * oBound ε * 128 =
      Nat.card (Zset t Q ψ) * (4 * Nat.card P) := by
        rw [hS.rad.card_P, hb, Nat.mul_div_cancel_left b (by norm_num)]; ring
    _ ≤ Nat.card (Zset t Q ψ) * Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) : Subgroup G) := Nat.mul_le_mul_left _ hS.four_mul_card_P_le
    _ = Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :=
        hS.card_normalizer_E.symm
    _ = Nat.card hS.affHom.range * 128 := h2.symm.trans h1.symm

theorem exists_aff_eq_of_mem_Zset
    (hZ : ∀ s, qfV ε s = 0 → s ∈ Zset t Q ψ) {v : V6} (hv : v ∈ Zset t Q ψ) :
    ∃ k ∈ Kgrp t Q, aff t ψ k 0 = v := by
  obtain ⟨k, hk, hkt⟩ := hv
  have hkK : k ∈ Kgrp t Q := ⟨hk, hS.normalizer_E_le_Q hZ hk⟩
  exact ⟨k, hkK, hS.tψ_injective (by rw [← hS.conj_t_aff hkK, hkt])⟩

theorem aff_mem_Zset (hZ : ∀ s, qfV ε s = 0 → s ∈ Zset t Q ψ)
    {g : G} (hg : g ∈ Kgrp t Q) {v : V6} (hv : v ∈ Zset t Q ψ) : aff t ψ g v ∈ Zset t Q ψ := by
  obtain ⟨k, hk, rfl⟩ := hS.exists_aff_eq_of_mem_Zset hZ hv
  rw [← hS.aff_mul hg hk]
  exact hS.aff_zero_mem_Zset (mul_mem hg hk)

end Setting

end CFSG.EvenSmallLie.OmegaEight.CPrime
