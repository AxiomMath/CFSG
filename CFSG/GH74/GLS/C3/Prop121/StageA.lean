module

public import CFSG.GH74.GLS.C3.Prop121.TU
public import CFSG.GH74.GLS.C3.Prop121.G67
public import CFSG.GH74.GLS.C3.Prop121.FnFacts
public import CFSG.GH74.GLS.C3.Prop121.PatternFacts
public import CFSG.GH74.GLS.C3.Prop121.MooreBasic

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup CFSG.GH74.GLS

@[expose] def S_gFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G ≤ 4 → ∀ (x : G) (K T Q S : Subgroup G) (a : G),
    IsAConfig 5 x K T Q S a → IsApproxTo G (alternatingGroup (Fin 9)) →
      ∃ g : G, g ^ 2 = 1 ∧ ∀ q ∈ Q, g * q * g⁻¹ ∈ K

theorem gt_mem_K {G : Type} [Group G] {n : ℕ} {x : G} {K Q : Subgroup G} {t u g : G}
    (hS : Stage3Base n x K Q t u) (hg2 : g ^ 2 = 1) (hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ K)
    (hCQ : ∀ c : G, (∀ q ∈ Q, c * q = q * c) → ∃ k ∈ K, ∃ q ∈ Q, c = k * q) :
    g * t * g⁻¹ ∈ K := by
  have hginv : g⁻¹ = g := sq_eq_one_inv hg2
  have hcomm : ∀ q ∈ Q, (g * t * g⁻¹) * q = q * (g * t * g⁻¹) := by
    intro q hq
    have h1 : t * (g * q * g⁻¹) = (g * q * g⁻¹) * t := hS.t_comm_K _ (hgQ q hq)
    have e : g⁻¹ * q * g = g * q * g⁻¹ := by rw [hginv]
    have h1' : t * (g⁻¹ * q * g) = (g⁻¹ * q * g) * t := by rw [e]; exact h1
    calc (g * t * g⁻¹) * q = g * (t * (g⁻¹ * q * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * q * g) * t) * g⁻¹ := by rw [h1']
      _ = q * (g * t * g⁻¹) := by group
  obtain ⟨k, hk, q, hq, hkq⟩ := hCQ _ hcomm
  have ht3 : t ^ 3 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hS.t_order] at this
  have h3 : (g * t * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, ht3]; group
  rw [hkq, (show Commute k q from hS.K_comm_Q k hk q hq).mul_pow] at h3
  have hq3 : q ^ 3 = q := by
    have : q ^ 3 = q ^ 2 * q := pow_succ q 2
    rw [this, hS.Q_sq q hq, one_mul]
  rw [hq3] at h3
  have hqK : q ∈ K := by
    have : q = (k ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h3
    rw [this]
    exact K.inv_mem (K.pow_mem hk 3)
  have hq1 : q = 1 := hS.K_inf_Q q hqK hq
  rw [hkq, hq1, mul_one]
  exact hk

theorem stage3Loc_of_g {G : Type} [Group G] [Finite G] {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7)
    (hG4 : pRank 2 G ≤ 4) {x : G} {K T Q S : Subgroup G} {a : G} (h : IsAConfig n x K T Q S a)
    (hF : FnFacts n) (hP : PatternFacts G n) {g : G} (hg2 : g ^ 2 = 1)
    (hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ K) : ∃ t u : G, Stage3Loc n x K Q t u g := by
  have hCQ := centralizer_Q_eq hn hG4 h hF
  have hn5 : 5 ≤ n := by omega
  have hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q = q * k := fun k hk q hq => ((h.mem_Q_iff q).1 hq).2 k hk
  have hKQ1 : ∀ k ∈ K, k ∈ Q → k = 1 := fun k hk hkQ => by
    have h1 : k ∈ K ⊓ Q := ⟨hk, hkQ⟩
    rw [h.K_inf_Q hn5] at h1
    exact Subgroup.mem_bot.1 h1
  obtain ⟨u, hu2, hux, huK, huKQ, huQ, huN⟩ := exists_u0 hn hG4 h
  obtain ⟨t, ht⟩ := exists_t_u hn h.x_sq h.x_ne_one h.x_mem_Q h.card_Q (fun q hq => h.Q_sq hq)
    (fun q hq r hr => h.Q_comm hq hr) h.K_equiv_alt hKQ hKQ1 hCQ (transitive hn hG4 h hF hP) hu2 hux
    huK huKQ huQ huN (K_norm hn hG4 h hF)
  exact ⟨t, u, { ht with g_sq := hg2, g_Q := hgQ, gt_K := gt_mem_K ht hg2 hgQ hCQ }⟩

theorem s_stage3Loc_of
    (hG5 : S_gFive) : S_stage3Loc := by
  intro G _ _ hC n hn x K T Q S a h hap
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hn
  have hG4 : pRank 2 G ≤ 4 := hC
  have hF := fnFacts n hn'
  have hP := patternFacts_of_approx hn' hap
  obtain ⟨g, hg2, hgQ⟩ : ∃ g : G, g ^ 2 = 1 ∧ ∀ q ∈ Q, g * q * g⁻¹ ∈ K := by
    rcases hn' with rfl | rfl | rfl
    · exact hG5 G hC x K T Q S a h hap
    · exact exists_g_six_seven hC (Or.inl rfl) h
    · exact exists_g_six_seven hC (Or.inr rfl) h
  obtain ⟨t, u, hS⟩ := stage3Loc_of_g hn' hG4 h hF hP hg2 hgQ
  exact ⟨t, u, g, hS⟩

end CFSG.GH74.GLS.C3.Prop121
