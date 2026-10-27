module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3G2V

public section

namespace CFSG.ComponentClassification.AS81.G2

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

theorem g2N_r_mul_q
    (A C D E F c D' f : K) :
    g2N A 0 C D E F * g2N 0 0 c D' 0 f = g2N A 0 (C + c) (D + D') E (F + c * D + f) := by
  rw [mul_g2N, pinnedX_zero, mul_one, pinnedX_zero, mul_one, g2N_mul_u, g2N_mul_v,
    pinnedX_zero, mul_one, g2N_mul_c]

theorem g2N_q_mul_r
    (c D' f A C D E F : K) :
    g2N 0 0 c D' 0 f * g2N A 0 C D E F =
      g2N A 0 (c + C) (D' + D) (c * A ^ 2 + D' * A + E) (f + c ^ 2 * A + C * D' + F) := by
  rw [mul_g2N, g2N_mul_r, pinnedX_zero, mul_one, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
  exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem g2ShortParabolicRadical_inf_normalizer_g2Q0_le
    [Finite K] (hK : Nat.card K = 4) {l : K} (hl : l ≠ 0) :
    g2ShortParabolicRadical K ⊓ normalizer (g2Q0 K l : Set (ModGL .G2 K)) ≤
      g2Q0 K l ⊔ g2BCGroup K := by
  rintro _ ⟨⟨A, C, D, E, F, rfl⟩, hN⟩
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
  have hω2 := sq_add_self_add_one_of_ne hK hω0 hω1
  have hω3 := pow_three_eq_one_of_ne hK hω0
  have key : ∀ c f : K, f ^ 2 + l * f + l ^ 2 * c ^ 3 = 0 →
      c * A ^ 2 + l * c ^ 2 * A = 0 ∧
        (f + (c * D + c ^ 2 * A + l * c ^ 2 * C)) ^ 2 +
          l * (f + (c * D + c ^ 2 * A + l * c ^ 2 * C)) + l ^ 2 * c ^ 3 = 0 := by
    intro c f hf
    have hq : g2N 0 0 c (l * c ^ 2) 0 f ∈ g2Q0 K l := ⟨c, f, pow_four_eq_self hK c, hf, rfl⟩
    obtain ⟨c', f', -, hf', heq⟩ := (mem_normalizer_iff.mp hN _).mp hq
    have h2 : g2N A 0 C D E F * g2N 0 0 c (l * c ^ 2) 0 f =
        g2N 0 0 c' (l * c' ^ 2) 0 f' * g2N A 0 C D E F := by
      rw [← heq]
      group
    rw [g2N_r_mul_q, g2N_q_mul_r] at h2
    obtain ⟨-, -, hC, -, hE, hF⟩ := g2N_injective h2
    have hc : c' = c := by linear_combination (norm := char2_ring) hC
    subst hc
    refine ⟨by linear_combination (norm := char2_ring) hE, ?_⟩
    have hf'' : f' = f + (c' * D + c' ^ 2 * A + l * c' ^ 2 * C) := by
      linear_combination (norm := char2_ring) hF
    rw [← hf'']
    exact hf'
  have hf1 : (l * ω) ^ 2 + l * (l * ω) + l ^ 2 * (1 : K) ^ 3 = 0 := by
    linear_combination l ^ 2 * hω2
  have hfω : (l * ω) ^ 2 + l * (l * ω) + l ^ 2 * ω ^ 3 = 0 := by
    rw [hω3]
    linear_combination l ^ 2 * hω2
  obtain ⟨hA1, hD1⟩ := key 1 (l * ω) hf1
  obtain ⟨hAω, hDω⟩ := key ω (l * ω) hfω
  have hA : A = 0 := by
    have h : l * A = 0 := by
      linear_combination (norm := char2_ring) ω * hA1 + hAω + (l * A) * hω2
    exact (mul_eq_zero.mp h).resolve_left hl
  subst hA
  have hg1 : (D + l * C) ^ 2 + l * (D + l * C) = 0 := by
    linear_combination (norm := char2_ring) hD1 - l ^ 2 * hω2
  have hgω : (ω * D + l * ω ^ 2 * C) ^ 2 + l * (ω * D + l * ω ^ 2 * C) = 0 := by
    rw [hω3] at hDω
    linear_combination (norm := char2_ring) hDω - l ^ 2 * hω2
  have hD : D = l * C ^ 2 := by
    have h : l * (l * (C ^ 2 + C) + (D + l * C)) = 0 := by
      linear_combination (norm := char2_ring) hgω - ω ^ 2 * hg1 + (l * (D + l * C)) * hω2 +
        (l ^ 2 * C + l ^ 2 * C ^ 2 * (ω ^ 2 + ω + 1)) * hω2
    have h' := (mul_eq_zero.mp h).resolve_left hl
    linear_combination (norm := char2_ring) h'
  subst hD
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : K, F₀ ^ 2 + l * F₀ + l ^ 2 * C ^ 3 = 0 := by
    by_cases hC0 : C = 0
    · exact ⟨0, by rw [hC0]; ring⟩
    · refine ⟨l * ω, ?_⟩
      rw [pow_three_eq_one_of_ne hK hC0]
      linear_combination l ^ 2 * hω2
  have hq₀ : g2N 0 0 C (l * C ^ 2) 0 F₀ ∈ g2Q0 K l := ⟨C, F₀, pow_four_eq_self hK C, hF₀, rfl⟩
  have hw : g2N 0 0 0 0 E (F + F₀) ∈ g2BCGroup K := ⟨E, F + F₀, rfl⟩
  have e : g2N 0 0 C (l * C ^ 2) E F = g2N 0 0 C (l * C ^ 2) 0 F₀ * g2N 0 0 0 0 E (F + F₀) := by
    rw [g2N_uv_mul]
    exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by ring) (by char2_ring)
  rw [e]
  exact mul_mem_sup hq₀ hw

end CFSG.ComponentClassification.AS81.G2
