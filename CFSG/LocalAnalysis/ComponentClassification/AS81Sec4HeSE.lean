module

public import CFSG.Foundations.Basic
import CFSG.GH74.GLS.Stage12.McLEndgame
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ComponentClassification.AS81.HeSE

open Subgroup CFSG.GH74.GLS.Stage12

section Fusion

variable {G : Type*} [Group G]

theorem isStronglyEmbedded_of_fusion [Finite G] (H : Subgroup G) (hH : H ≠ ⊤)
    (hev : Even (Nat.card H))
    (hfus : ∀ u ∈ H, orderOf u = 2 → ∀ g : G, g * u * g⁻¹ ∈ H →
      ∃ c ∈ H, c * u * c⁻¹ = g * u * g⁻¹)
    (hcent : ∀ u ∈ H, orderOf u = 2 → centralizer ({u} : Set G) ≤ H) :
    CFSG.IsStronglyEmbedded H := by
  refine ⟨hH, hev, fun g hg => ?_⟩
  by_contra hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ CFSG.conjugate H g)) 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
  have hxo : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxH : (x : G) ∈ H := (mem_inf.mp x.2).1
  have hxg : g * (x : G) * g⁻¹ ∈ H := (McLRec.mem_conjugate_iff H g x).mp (mem_inf.mp x.2).2
  obtain ⟨c, hcH, hc⟩ := hfus x hxH hxo g hxg
  have hgc : g⁻¹ * c ∈ centralizer ({(x : G)} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * c * (x : G) = g⁻¹ * (c * x * c⁻¹) * c := by group
      _ = g⁻¹ * (g * x * g⁻¹) * c := by rw [hc]
      _ = x * (g⁻¹ * c) := by group
  have h1 : g⁻¹ * c ∈ H := hcent x hxH hxo hgc
  exact hg (by simpa using H.mul_mem hcH (H.inv_mem h1))

theorem fusion_of_reps (H : Subgroup G) (T : Set G)
    (hT : ∀ u ∈ H, orderOf u = 2 → ∃ t ∈ T, ∃ c ∈ H, c * u * c⁻¹ = t)
    (hTT : ∀ t ∈ T, ∀ t' ∈ T, ∀ g : G, g * t * g⁻¹ = t' → ∃ c ∈ H, c * t * c⁻¹ = t') :
    ∀ u ∈ H, orderOf u = 2 → ∀ g : G, g * u * g⁻¹ ∈ H →
      ∃ c ∈ H, c * u * c⁻¹ = g * u * g⁻¹ := by
  intro u hu hu2 g hv
  obtain ⟨t, ht, c₁, hc₁, h₁⟩ := hT u hu hu2
  have hv2 : orderOf (g * u * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hu2
  obtain ⟨t', ht', c₂, hc₂, h₂⟩ := hT _ hv hv2
  obtain ⟨c₃, hc₃, h₃⟩ := hTT t ht t' ht' (c₂ * g * c₁⁻¹) (by rw [← h₁, ← h₂]; group)
  refine ⟨c₂⁻¹ * c₃ * c₁, H.mul_mem (H.mul_mem (H.inv_mem hc₂) hc₃) hc₁, ?_⟩
  calc c₂⁻¹ * c₃ * c₁ * u * (c₂⁻¹ * c₃ * c₁)⁻¹ =
        c₂⁻¹ * (c₃ * (c₁ * u * c₁⁻¹) * c₃⁻¹) * c₂ := by group
    _ = c₂⁻¹ * (c₂ * (g * u * g⁻¹) * c₂⁻¹) * c₂ := by rw [h₁, h₃, h₂]
    _ = g * u * g⁻¹ := by group

end Fusion

section SE

variable {G : Type} [Group G] [Finite G]

theorem false_of_isStronglyEmbedded (hs : IsSimpleGroup G)
    {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) (hV4 : Nat.card V = 4) {M : Subgroup G}
    (hM : CFSG.IsStronglyEmbedded M)
    (hB : ∀ S : Subgroup G, IsPGroup 2 S → Nat.card S = 2 ^ (Nat.card G).factorization 2 →
      S ≤ M → M ≤ normalizer (S : Set G) → False) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrank : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) := by
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨V, le_top, hV, by rw [hV4]; norm_num⟩
    rintro r ⟨B, -, -, hB⟩
    calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group B
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 (by rw [hV4]; norm_num)
  have hv2 : orderOf (v : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hv
  have hL := McLRec.involutionClosure_eq_top hs hv2
  have hev : Even (Nat.card G) := even_iff_two_dvd.mpr
    (((by rw [hV4]; norm_num : 2 ∣ Nat.card V)).trans (Subgroup.card_subgroup_dvd_card V))
  rcases CFSG.GH74.Uniqueness.S_SE_proof G M hM with h | ⟨-, -, hBor⟩
  · rw [hL] at h
    omega
  · obtain ⟨S, hSp, hScard, hSM, hMN⟩ :=
      McLRec.exists_sylow_normalized_of_borel hs hev _ hL M hBor
    exact hB S hSp hScard hSM hMN

theorem eq_top_of_fusion (hs : IsSimpleGroup G) {V : Subgroup G}
    (hV : CFSG.Open.IsElemAbelian 2 V) (hV4 : Nat.card V = 4) (H : Subgroup G)
    (hev : Even (Nat.card H))
    (hfus : ∀ u ∈ H, orderOf u = 2 → ∀ g : G, g * u * g⁻¹ ∈ H →
      ∃ c ∈ H, c * u * c⁻¹ = g * u * g⁻¹)
    (hcent : ∀ u ∈ H, orderOf u = 2 → centralizer ({u} : Set G) ≤ H)
    (hB : ∀ S : Subgroup G, IsPGroup 2 S → Nat.card S = 2 ^ (Nat.card G).factorization 2 →
      S ≤ H → H ≤ normalizer (S : Set G) → False) : H = ⊤ := by
  by_contra hH
  exact false_of_isStronglyEmbedded hs hV hV4
    (isStronglyEmbedded_of_fusion H hH hev hfus hcent) hB

end SE

end CFSG.ComponentClassification.AS81.HeSE
