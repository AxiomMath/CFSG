module

public import CFSG.GH74.GLS.C3.Prop121.MooreR7b
public import CFSG.GH74.GLS.C3.Prop121.MooreFinite
public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2

namespace MCtx

variable {G : Type} [Group G] {n : ℕ} {x : G} {K Q : Subgroup G} {t u g : G} {L : Subgroup G}
  {φ : Perm (Fin (n + 1)) →* G}

theorem R7
    (h : MCtx n x K Q t u g L φ) : (x * φ (cs n 0)) ^ 3 = 1 := by
  obtain ⟨σ1, hσY, hσ2, hσL, hσt, hσx, hσa⟩ := h.exists_sigma
  have hn5 := h.n_ge
  obtain ⟨s1, hs1⟩ := h.P.surj _ (h.K_le_Y h.xg_mem)
  obtain ⟨sg, hsg⟩ := h.P.surj _ hσY
  have hex : ∀ k : ℕ, ∃ p : Perm (Fin (n + 1)), k + 4 ≤ n → φ p = g * φ (cs n k) * g⁻¹ := by
    intro k
    by_cases hk : k + 4 ≤ n
    · obtain ⟨p, hp⟩ := h.P.surj _ (mem_sup_left (h.a_mem_L hk))
      exact ⟨p, fun _ => hp⟩
    · exact ⟨1, fun h' => absurd h' hk⟩
  choose S hS using hex
  have hcg : φ (cEnd n) = g * t * g⁻¹ := h.hc
  have hxg2 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
    calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [h.x_mul_self]; group
  have F1 : s1 * s1 = 1 := h.P.inj (by rw [map_mul, hs1, map_one]; exact hxg2)
  have F2 : sign s1 = 1 := (h.P.alt s1).1 (by rw [hs1]; exact h.C.K_le_L h.xg_mem)
  have F3 : s1 ≠ 1 := by
    intro h1
    apply h.S.x_ne
    have h2 : g * x * g⁻¹ = 1 := by rw [← hs1, h1, map_one]
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h2]; group
  have F4 : (cEnd n * s1) ^ 3 = 1 := by
    apply h.P.inj
    rw [map_pow, map_mul, hcg, hs1, map_one]
    have e : g * t * g⁻¹ * (g * x * g⁻¹) = g * (t * x) * g⁻¹ := by group
    rw [e, conj_pow, h.S.tx_cube]
    group
  have H1 : sg * sg = 1 := h.P.inj (by rw [map_mul, hsg, map_one]; exact hσ2)
  have H2 : sign sg = -1 := by
    have : ¬ sign sg = 1 := fun h1 => hσL (by rw [← hsg]; exact (h.P.alt sg).2 h1)
    rcases Int.units_eq_one_or (sign sg) with h1 | h1
    · exact absurd h1 this
    · exact h1
  have H3 : sg * cEnd n * sg⁻¹ = (cEnd n)⁻¹ := by
    apply h.P.inj
    rw [map_mul, map_mul, map_inv, map_inv, hsg, hcg]
    exact hσt
  have H4 : sg * s1 = s1 * sg := by
    apply h.P.inj
    rw [map_mul, map_mul, hsg, hs1]
    exact hσx
  have G1 : ∀ k, k + 4 ≤ n → S k * S k = 1 ∧ sign (S k) = 1 ∧
      S k * cEnd n * (S k)⁻¹ = (cEnd n)⁻¹ ∧ sg * S k = S k * sg := by
    intro k hk
    have hSk := hS k hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply h.P.inj
      rw [map_mul, hSk, map_one]
      calc (g * φ (cs n k) * g⁻¹) * (g * φ (cs n k) * g⁻¹)
          = g * (φ (cs n k) * φ (cs n k)) * g⁻¹ := by group
        _ = 1 := by rw [← map_mul, cs_mul_self, map_one]; group
    · exact (h.P.alt _).1 (by rw [hSk]; exact h.a_mem_L hk)
    · apply h.P.inj
      rw [map_mul, map_mul, map_inv, map_inv, hSk, hcg]
      exact h.a_inv_tg (by omega)
    · apply h.P.inj
      rw [map_mul, map_mul, hsg, hSk]
      exact hσa k hk
  have G2 : ∀ k, 1 ≤ k → k + 4 ≤ n → S k * s1 = s1 * S k := by
    intro k hk1 hk
    apply h.P.inj
    rw [map_mul, map_mul, hs1, hS k hk]
    exact h.a_comm_xg hk1
  have G3 : ∀ k, k + 5 ≤ n → (S k * S (k + 1)) ^ 3 = 1 := by
    intro k hk
    apply h.P.inj
    rw [map_pow, map_mul, hS k (by omega), hS (k + 1) (by omega), map_one]
    exact MCtx.a_braid (φ := φ) (g := g) (by omega)
  have G4 : ∀ k l, k + 2 ≤ l → l + 4 ≤ n → (S k * S l) ^ 2 = 1 := by
    intro k l hkl hl
    apply h.P.inj
    rw [map_pow, map_mul, hS k (by omega), hS l hl, map_one]
    exact MCtx.a_sq2 (φ := φ) (g := g) hkl
  have G5 : ∀ k l, k < l → l + 4 ≤ n → S k ≠ S l := by
    intro k l hkl hl heq
    apply h.a_ne (by omega : k < n) (by omega : l < n) (by omega : k ≠ l)
    rw [← hS k (by omega), ← hS l hl, heq]
  have hfin : (s1 * S 0) ^ 3 = 1 := by
    rcases h.hn with rfl | rfl | rfl
    · obtain ⟨a2, b2, c2, d2⟩ := G1 0 (by norm_num)
      obtain ⟨a3, b3, c3, d3⟩ := G1 1 (by norm_num)
      exact moore_finite_five (cEnd 5) (by decide) s1 sg (S 0) (S 1) ⟨F1, F2, F3, F4⟩
        ⟨H1, H2, H3, H4⟩ ⟨a2, b2, c2, d2⟩
        ⟨a3, b3, c3, d3, G2 1 le_rfl (by norm_num), G3 0 (by norm_num),
          G5 0 1 (by norm_num) (by norm_num)⟩
    · obtain ⟨a2, b2, c2, d2⟩ := G1 0 (by norm_num)
      obtain ⟨a3, b3, c3, d3⟩ := G1 1 (by norm_num)
      obtain ⟨a4, b4, c4, d4⟩ := G1 2 (by norm_num)
      exact moore_finite_six (cEnd 6) (by decide) s1 sg (S 0) (S 1) (S 2) ⟨F1, F2, F3, F4⟩
        ⟨H1, H2, H3, H4⟩ ⟨a2, b2, c2, d2⟩
        ⟨a3, b3, c3, d3, G2 1 le_rfl (by norm_num), G3 0 (by norm_num),
          G5 0 1 (by norm_num) (by norm_num)⟩
        ⟨a4, b4, c4, d4, G2 2 (by norm_num) (by norm_num), G3 1 (by norm_num),
          G4 0 2 (by norm_num) (by norm_num), G5 0 2 (by norm_num) (by norm_num)⟩
    · obtain ⟨a2, b2, c2, d2⟩ := G1 0 (by norm_num)
      obtain ⟨a3, b3, c3, d3⟩ := G1 1 (by norm_num)
      obtain ⟨a4, b4, c4, d4⟩ := G1 2 (by norm_num)
      obtain ⟨a5, b5, c5, d5⟩ := G1 3 (by norm_num)
      exact moore_finite_seven (cEnd 7) (by decide) s1 sg (S 0) (S 1) (S 2) (S 3)
        ⟨F1, F2, F3, F4⟩ ⟨H1, H2, H3, H4⟩ ⟨a2, b2, c2, d2⟩
        ⟨a3, b3, c3, d3, G2 1 le_rfl (by norm_num), G3 0 (by norm_num),
          G5 0 1 (by norm_num) (by norm_num)⟩
        ⟨a4, b4, c4, d4, G2 2 (by norm_num) (by norm_num), G3 1 (by norm_num),
          G4 0 2 (by norm_num) (by norm_num), G5 0 2 (by norm_num) (by norm_num)⟩
        ⟨a5, b5, c5, d5, G2 3 (by norm_num) (by norm_num), G3 2 (by norm_num),
          G4 0 3 (by norm_num) (by norm_num), G4 1 3 (by norm_num) (by norm_num)⟩
  have h3 := congrArg φ hfin
  rw [map_pow, map_mul, hs1, hS 0 (by omega), map_one] at h3
  have e : g * x * g⁻¹ * (g * φ (cs n 0) * g⁻¹) = g * (x * φ (cs n 0)) * g⁻¹ := by group
  rw [e, conj_pow] at h3
  calc (x * φ (cs n 0)) ^ 3 = g⁻¹ * (g * (x * φ (cs n 0)) ^ 3 * g⁻¹) * g := by group
    _ = 1 := by rw [h3]; group

end MCtx

end CFSG.GH74.GLS.C3.Prop121
