module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiYBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem swapT_card_eq_of_index_two (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hidx : ∀ s ∈ T, ∀ s' ∈ T, s ∉ szT₁ L T ⊔ zpowers t → s' ∉ szT₁ L T ⊔ zpowers t →
      s * s'⁻¹ ∈ szT₁ L T ⊔ zpowers t)
    {y : G} (hyT : y ∈ T) (hyH : y ∉ szT₁ L T ⊔ zpowers t) :
    T ≤ (szT₁ L T ⊔ zpowers t) ⊔ zpowers y ∧
      Nat.card ((szT₁ L T ⊔ zpowers t) ⊔ zpowers y : Subgroup G) = 4 * (2 ^ f) ^ 3 := by
  obtain ⟨htT, -, -, -, -, hMn, -⟩ := h.start_of_card_sylow hS2
  set H := szT₁ L T ⊔ zpowers t with hHdef
  have hHT : H ≤ T := sup_le (szT₁_le_left L T) (zpowers_le.mpr htT)
  have hyN : y ∈ normalizer (H : Set G) := by
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun m hm => ?_
    have := hMn.conj_mem ⟨m, hHT hm⟩ (mem_subgroupOf.mpr hm) ⟨y⁻¹, inv_mem hyT⟩
    simpa using mem_subgroupOf.mp this
  have hy' : y⁻¹ ∉ H := fun h' => hyH (by simpa using inv_mem h')
  have hyy : y * y ∈ H := by
    have := hidx y hyT y⁻¹ (inv_mem hyT) hyH hy'
    rwa [inv_inv] at this
  refine ⟨fun s hs => ?_, ?_⟩
  · by_cases hsH : s ∈ H
    · exact mem_sup_left hsH
    · have h1 := hidx s hs y hyT hsH hyH
      rw [show s = (s * y⁻¹) * y by group]
      exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers y))
  · have h2 := relIndex_sup_zpowers_eq_two_of_mul_self_mem hyH hyN hyy
    have h3 := relIndex_mul_card (H := H) (K := H ⊔ zpowers y)
    rw [h2, inf_of_le_left le_sup_left, h.card_szT₁_sup_of_card_sylow hS2] at h3
    omega

theorem swapT_card_le_of_comm (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hidx : ∀ s ∈ T, ∀ s' ∈ T, s ∉ szT₁ L T ⊔ zpowers t → s' ∉ szT₁ L T ⊔ zpowers t →
      s * s'⁻¹ ∈ szT₁ L T ⊔ zpowers t)
    {B : Subgroup G} (hBT : B ≤ T) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    Nat.card B ≤ 2 * (2 ^ f) ^ 2 := by
  obtain ⟨htT, -, -, hTN₁, hdisj, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, -, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  set H := szT₁ L T ⊔ zpowers t with hHdef
  have hB1 := relIndex_mul_card (H := szT₁ L T) (K := B)
  have hBab : Nat.card (szT₁ L T ⊓ B : Subgroup G) ≤ (2 ^ f) ^ 2 :=
    h.card_le_of_comm_of_card_sylow hS2 inf_le_left fun x hx y hy =>
      hBc x (mem_inf.mp hx).2 y (mem_inf.mp hy).2
  by_cases hBH : B ≤ H
  ·
    have htt : t * t = 1 := by rw [← sq, h.sq_eq_one]
    have htT₁ : t ∉ szT₁ L T := fun h' => by
      have ht1 : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨h', mem_zpowers t⟩
      rw [hdisj, mem_bot] at ht1
      have h1 := h.inv
      rw [ht1, orderOf_one] at h1
      exact absurd h1 (by norm_num)
    have htN : t ∈ normalizer (szT₁ L T : Set G) := hTN₁ htT
    have h2 := RankOne.Endings.relIndex_sup_zpowers_eq_two htT₁ htN htt
    have hne : (szT₁ L T).relIndex H ≠ 0 := by rw [h2]; norm_num
    have h3 := Subgroup.relIndex_le_of_le_right hBH hne
    rw [h2] at h3
    calc Nat.card B = (szT₁ L T).relIndex B * Nat.card (szT₁ L T ⊓ B : Subgroup G) := hB1.symm
      _ ≤ 2 * (2 ^ f) ^ 2 := Nat.mul_le_mul h3 hBab
  ·
    obtain ⟨y, hyB, hyH⟩ : ∃ y ∈ B, y ∉ H := by
      by_contra hcon
      push Not at hcon
      exact hBH hcon
    have hyT := hBT hyB
    obtain ⟨E, _, _, _, σ, u, v, hSC⟩ := h.exists_semilinearCoords_of_card_sylow hS2
    have hcent := U3SemilinearCoords.card_centralizer_le hSC h hS2 hyT hyH
    have hA : Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ 2 ^ f := by
      rw [← hA₁card]
      exact Subgroup.card_le_of_le inf_le_left
    have hBC : szT₁ L T ⊓ B ≤ szT₁ L T ⊓ centralizer ({y} : Set G) := fun z hz =>
      mem_inf.mpr ⟨(mem_inf.mp hz).1,
        mem_centralizer_singleton_iff.mpr (hBc z (mem_inf.mp hz).2 y hyB)⟩
    have hBy : Nat.card (szT₁ L T ⊓ B : Subgroup G) ≤ 2 * 2 ^ f :=
      (Subgroup.card_le_of_le hBC).trans (hcent.trans (Nat.mul_le_mul_left 2 hA))
    obtain ⟨hTK, hKcard⟩ := h.swapT_card_eq_of_index_two hS2 hidx hyT hyH
    set K := H ⊔ zpowers y with hKdef
    have hT₁K : szT₁ L T ≤ K := le_sup_left.trans le_sup_left
    have hK1 := relIndex_mul_card (H := szT₁ L T) (K := K)
    rw [inf_of_le_left hT₁K, hT₁card, hKcard] at hK1
    have hK4 : (szT₁ L T).relIndex K = 4 := by
      have hq3 : 0 < (2 ^ f) ^ 3 := pow_pos (pow_pos (by norm_num) f) 3
      exact Nat.eq_of_mul_eq_mul_right hq3 hK1
    have hne : (szT₁ L T).relIndex K ≠ 0 := by rw [hK4]; norm_num
    have h3 := Subgroup.relIndex_le_of_le_right (hBT.trans hTK) hne
    rw [hK4] at h3
    calc Nat.card B = (szT₁ L T).relIndex B * Nat.card (szT₁ L T ⊓ B : Subgroup G) := hB1.symm
      _ ≤ 4 * (2 * 2 ^ f) := Nat.mul_le_mul h3 hBy
      _ = 2 * (4 * 2 ^ f) := by ring
      _ ≤ 2 * (2 ^ f * 2 ^ f) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hq4)
      _ = 2 * (2 ^ f) ^ 2 := by ring

end U3Start

end CFSG.SeitzReduction.RankOne
