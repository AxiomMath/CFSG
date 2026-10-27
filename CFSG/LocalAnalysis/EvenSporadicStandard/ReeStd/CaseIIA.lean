module

import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Frattini

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

namespace Stage

variable {H : LocalSetting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem exists_sylow_N (hS : 2 ∣ S.index) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ S ≤ T ∧ T ≤ normalizer (S : Set G) ∧
      Nat.card T = 8 * Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTp, hST, hTN, hTodd⟩ := exists_isPGroup_le_odd_relIndex
    (A := normalizer (S : Set G)) h.pgroup (le_normalizer : S ≤ normalizer (S : Set G))
  refine ⟨T, hTp, hST, hTN, ?_⟩
  obtain ⟨a, ha⟩ := hTp.exists_card_eq
  obtain ⟨b, hb⟩ := h.pgroup.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card (H := T) (K := normalizer (S : Set G))
  rw [inf_eq_left.2 hTN] at h1
  have hN := h.card_N hS
  have hDC := h.card_DC
  have hS2 := h.card_S
  refine eq_of_odd_mul_eq ⟨a, ha⟩ ⟨b + 3, ?_⟩ hTodd
    (d := 21 * H.V.relIndex (H.DC S)) (Odd.mul (by decide) h.odd_relIndex_V_DC) ?_
  · rw [pow_add, ← hb]
    ring
  · calc Nat.card T * T.relIndex (normalizer (S : Set G))
        = T.relIndex (normalizer (S : Set G)) * Nat.card T := mul_comm _ _
      _ = Nat.card (normalizer (S : Set G) : Subgroup G) := h1
      _ = 21 * Nat.card Λ * Nat.card (H.DC S) := hN
      _ = 21 * Nat.card Λ * (H.V.relIndex (H.DC S) * 16) := by rw [hDC]
      _ = 8 * Nat.card S * (21 * H.V.relIndex (H.DC S)) := by rw [hS2]; ring

include h in
theorem exists_sq_of_mem_E (hΛ : 8 < Nat.card Λ) {e : G} (he : e ∈ H.E) :
    ∃ l ∈ Λ, e = l * l := by
  obtain ⟨σ, hσ, hσS⟩ := h.exists_sigma
  have hσΛ : σ ∈ normalizer (Λ : Set G) := h.N_le_normalizer_Λ hσS
  obtain ⟨l₀, hl₀, hl₀sq⟩ : ∃ l₀ ∈ Λ, l₀ * l₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : Λ ≤ H.E := fun l hl => h.mem_E_of_sq hl (hcon l hl)
    have := Subgroup.card_le_of_le hle
    rw [H.card_E] at this
    omega
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 h.pgroup ⟨l₀ * l₀, h.le (mul_mem hl₀ hl₀)⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hl₀sq (orderOf_eq_one_iff.1 hk)
  have hbΛ : (l₀ * l₀) ^ 2 ^ (k - 1) ∈ Λ := Subgroup.pow_mem Λ (mul_mem hl₀ hl₀) _
  have hbsq : (l₀ * l₀) ^ 2 ^ (k - 1) * (l₀ * l₀) ^ 2 ^ (k - 1) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk1),
      ← hk]
    exact pow_orderOf_eq_one _
  have hb1 : (l₀ * l₀) ^ 2 ^ (k - 1) ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hk]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hbE : (l₀ * l₀) ^ 2 ^ (k - 1) ∈ H.E := h.mem_E_of_sq hbΛ hbsq
  have hbc : (l₀ * l₀) ^ 2 ^ (k - 1) = l₀ ^ 2 ^ (k - 1) * l₀ ^ 2 ^ (k - 1) :=
    (Commute.refl l₀).mul_pow _
  by_cases he1 : e = 1
  · exact ⟨1, one_mem Λ, by rw [he1, mul_one]⟩
  obtain ⟨i, hi⟩ := hσ.trans hbE he hb1 he1
  refine ⟨σ ^ i * l₀ ^ 2 ^ (k - 1) * (σ ^ i)⁻¹, ?_, ?_⟩
  · have hσi : σ ^ i ∈ normalizer (Λ : Set G) := pow_mem hσΛ i
    exact (mem_normalizer_iff.1 hσi _).1 (Subgroup.pow_mem Λ hl₀ _)
  · rw [← hi, hbc]
    group

include h in
theorem caseII_conj_le (hcase : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ H.RC S → P ≤ S)
    (hΛ : 8 < Nat.card Λ) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hTN : T ≤ normalizer (S : Set G)) :
    ∀ x ∈ T, IsConj H.z x → x ∈ S := by
  intro x hxT hxc
  by_contra hxS
  have hxN : x ∈ normalizer (S : Set G) := hTN hxT
  have hx2 : x * x = 1 := H.sq_of_isConj hxc
  have hinv : ∀ l ∈ Λ, (l * l) * ((x * l * x⁻¹) * (x * l * x⁻¹)) = 1 := by
    intro l hl
    have hl' : x * l * x⁻¹ ∈ Λ := h.N_normalizes_Λ hxN hl
    have hcΛ : l * (x * l * x⁻¹) ∈ Λ := mul_mem hl hl'
    have hxcx : x * (l * (x * l * x⁻¹)) * x⁻¹ = l * (x * l * x⁻¹) :=
      calc x * (l * (x * l * x⁻¹)) * x⁻¹
          = (x * l * x⁻¹) * ((x * x) * l * (x * x)⁻¹) := by group
        _ = (x * l * x⁻¹) * l := by rw [hx2]; group
        _ = l * (x * l * x⁻¹) := h.comm hl' hl
    have hP : IsPGroup 2 (zpowers (l * (x * l * x⁻¹))) :=
      h.pgroup.to_le (zpowers_le.2 (h.le hcΛ))
    have hPC : zpowers (l * (x * l * x⁻¹)) ≤ centralizer ({x} : Set G) := by
      refine zpowers_le.2 (mem_centralizer_singleton_iff.2 ?_)
      calc l * (x * l * x⁻¹) * x = (x * (l * (x * l * x⁻¹)) * x⁻¹) * x := by rw [hxcx]
        _ = x * (l * (x * l * x⁻¹)) := by group
    have hcc := (H.star_conj hxc hP hPC).2 _ (mem_zpowers _)
    calc (l * l) * ((x * l * x⁻¹) * (x * l * x⁻¹))
        = l * (l * (x * l * x⁻¹)) * (x * l * x⁻¹) := by group
      _ = l * ((x * l * x⁻¹) * l) * (x * l * x⁻¹) := by rw [h.comm hl hl']
      _ = (l * (x * l * x⁻¹)) * (l * (x * l * x⁻¹)) := by group
      _ = 1 := hcc
  have hcent : ∀ e ∈ H.E, e * x = x * e := by
    intro e he
    obtain ⟨l, hl, rfl⟩ := h.exists_sq_of_mem_E hΛ he
    have h1 := hinv l hl
    have h2 : x * (l * l) * x⁻¹ = (l * l)⁻¹ := by
      have := eq_inv_of_mul_eq_one_right h1
      rw [← this]
      group
    have h3 : x * (l * l) * x⁻¹ = l * l := by rw [h2, H.E_inv he]
    calc l * l * x = (x * (l * l) * x⁻¹) * x := by rw [h3]
      _ = x * (l * l) := by group
  have hxR : x ∈ H.RC S := ⟨Subgroup.mem_centralizer_iff.2 hcent, hxN⟩
  exact hxS (hcase (zpowers x) (hT.to_le (zpowers_le.2 hxT)) (zpowers_le.2 hxR) (mem_zpowers x))

include h in
theorem caseII_not_two_dvd_index_of_conj_le
    {T : Subgroup G} (hT : IsPGroup 2 T) (hST : S ≤ T) (hTN : T ≤ normalizer (S : Set G))
    (hTcard : Nat.card T = 8 * Nat.card S)
    (hconj : ∀ x ∈ T, IsConj H.z x → x ∈ S) : ¬ 2 ∣ T.index := by
  have hVT : H.V ≤ T := h.V_le.trans hST
  have hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({H.z} : Set G) →
      centralizer ({H.z} : Set G) ⊓ T ≤ P → P ≤ T := by
    intro P hP hPC hTP
    have hVP : H.V ≤ P := (le_inf H.V_le_centralizer hVT).trans hTP
    have := Subgroup.eq_of_le_of_card_ge hVP (by rw [H.card_V]; exact (H.star hP hPC).1)
    rw [← this]
    exact hVT
  refine J1Std.not_two_dvd_index_of_invariant hT hmax fun n hn => ?_
  have hnz : n * H.z * n⁻¹ ∈ T := (mem_normalizer_iff.1 hn H.z).1 (hST h.z_mem)
  have hnc : IsConj H.z (n * H.z * n⁻¹) := _root_.isConj_iff.2 ⟨n, rfl⟩
  have hnS : n * H.z * n⁻¹ ∈ S := hconj _ hnz hnc
  have hnΛ : n * H.z * n⁻¹ ∉ Λ := fun hh => h.not_isConj_of_mem hh hnc
  obtain ⟨t, ht, e⟩ := h.exists_conj_z_of_card hT hST hTN hTcard hnS hnΛ
  exact ⟨t, ht, e⟩

end Stage

end CFSG.EvenSporadicStandard.ReeStd
