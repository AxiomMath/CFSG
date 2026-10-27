module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16P

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {K Y Q : Subgroup G} {t rho z u fz fu : G}

theorem c16_beta_zero_conj (H : C16Ab K Y Q t rho z u fz fu) {n : G}
    (hY : n ∈ normalizer (Y : Set G)) (hQ : n ∈ normalizer (Q : Set G)) {q : G} (hq : q ∈ Q) :
    c16Beta z u fz fu (n * q * n⁻¹) = 0 ↔ c16Beta z u fz fu q = 0 := by
  have hnq : n * q * n⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hQ q).mp hq
  rw [c16_beta_eq_zero_iff H hnq, c16_beta_eq_zero_iff H hq]
  constructor
  · intro h f hf
    have hnf : n * f * n⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hY f).mp hf
    have hc := h (n * f * n⁻¹) hnf
    calc q * f = n⁻¹ * ((n * q * n⁻¹) * (n * f * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * f * n⁻¹) * (n * q * n⁻¹)) * n := by rw [hc]
      _ = f * q := by group
  · intro h f hf
    have hnf : n⁻¹ * f * n ∈ Y := (Subgroup.mem_normalizer_iff''.mp hY f).mp hf
    have hc := h (n⁻¹ * f * n) hnf
    calc (n * q * n⁻¹) * f = n * (q * (n⁻¹ * f * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * f * n) * q) * n⁻¹ := by rw [hc]
      _ = f * (n * q * n⁻¹) := by group

theorem c16_beta_pplus_conj (H : C16Ab K Y Q t rho z u fz fu) {n : G}
    (hY : n ∈ normalizer (Y : Set G)) (hK : n ∈ normalizer (K : Set G))
    (hQ : n ∈ normalizer (Q : Set G)) {q : G} (hq : q ∈ Q) :
    c16Pplus (c16Beta z u fz fu (n * q * n⁻¹)) ↔ c16Pplus (c16Beta z u fz fu q) := by
  have hnq : n * q * n⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hQ q).mp hq
  rw [c16_beta_pplus H hnq, c16_beta_pplus H hq]
  constructor
  · rintro ⟨f, hfY, hfK, hfix⟩
    refine ⟨n⁻¹ * f * n, (Subgroup.mem_normalizer_iff''.mp hY f).mp hfY, ?_, ?_⟩
    · intro hf'K
      have hmem : n * (n⁻¹ * f * n) * n⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp hK (n⁻¹ * f * n)).mp hf'K
      have heq : n * (n⁻¹ * f * n) * n⁻¹ = f := by group
      rw [heq] at hmem
      exact hfK hmem
    · calc q * (n⁻¹ * f * n) * q⁻¹
          = n⁻¹ * ((n * q * n⁻¹) * f * (n * q * n⁻¹)⁻¹) * n := by group
        _ = n⁻¹ * f * n := by rw [hfix]
  · rintro ⟨f, hfY, hfK, hfix⟩
    refine ⟨n * f * n⁻¹, (Subgroup.mem_normalizer_iff.mp hY f).mp hfY, ?_, ?_⟩
    · intro hf'K
      exact hfK ((Subgroup.mem_normalizer_iff.mp hK f).mpr hf'K)
    · calc (n * q * n⁻¹) * (n * f * n⁻¹) * (n * q * n⁻¹)⁻¹
          = n * (q * f * q⁻¹) * n⁻¹ := by group
        _ = n * f * n⁻¹ := by rw [hfix]

theorem c16_beta_conj_t (H : C16Ab K Y Q t rho z u fz fu)
    (hQm : ∀ q ∈ Q, c16Qm (c16Beta z u fz fu q))
    (hsurj : ∀ w, c16Qm w → ∃ q ∈ Q, c16Beta z u fz fu q = w) (htQ : t ∈ Q) {n : G}
    (hY : n ∈ normalizer (Y : Set G)) (hK : n ∈ normalizer (K : Set G))
    (hQ : n ∈ normalizer (Q : Set G)) : c16Beta z u fz fu (n * t * n⁻¹) = c16T0 := by
  have hn : n⁻¹ ∈ normalizer (Q : Set G) := (normalizer (Q : Set G)).inv_mem hQ
  have ht₁Q : n * t * n⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hQ t).mp htQ
  refine c16_F5 (c16Beta z u fz fu (n * t * n⁻¹)) (hQm (n * t * n⁻¹) ht₁Q) ?_
  unfold c16Sep
  intro w hwQm hwne hwP
  obtain ⟨q₀, hq₀Q, hq₀β⟩ := hsurj w hwQm
  let q : G := n⁻¹ * q₀ * n
  have hqQ : q ∈ Q := by
    show n⁻¹ * q₀ * n ∈ Q
    simpa using (Subgroup.mem_normalizer_iff.mp hn q₀).mp hq₀Q
  have hnq : n * q * n⁻¹ = q₀ := by
    show n * (n⁻¹ * q₀ * n) * n⁻¹ = q₀
    group
  have hβq_ne : c16Beta z u fz fu q ≠ 0 := by
    intro h0
    have h1 : c16Beta z u fz fu (n * q * n⁻¹) = 0 :=
      (c16_beta_zero_conj H hY hQ hqQ).mpr h0
    rw [hnq, hq₀β] at h1
    exact hwne h1
  have hβqP : c16Pplus (c16Beta z u fz fu q) := by
    have h2 : c16Pplus (c16Beta z u fz fu (n * q * n⁻¹)) := by
      rw [hnq, hq₀β]
      exact hwP
    exact (c16_beta_pplus_conj H hY hK hQ hqQ).mp h2
  have htq_good : c16Good (c16Beta z u fz fu (t * q)) := by
    have hadd : c16Beta z u fz fu (t * q) = c16T0 + c16Beta z u fz fu q := by
      rw [c16_beta_add H htQ hqQ, c16_beta_t H]
    rw [hadd]
    exact c16_F4 (c16Beta z u fz fu q) (hQm q hqQ) hβq_ne hβqP
  have htqQ : t * q ∈ Q := Q.mul_mem htQ hqQ
  have hconj : n * (t * q) * n⁻¹ = (n * t * n⁻¹) * q₀ := by
    show n * (t * (n⁻¹ * q₀ * n)) * n⁻¹ = (n * t * n⁻¹) * q₀
    group
  have hgood' : c16Good (c16Beta z u fz fu ((n * t * n⁻¹) * q₀)) := by
    have hz : c16Beta z u fz fu ((n * t * n⁻¹) * q₀) ≠ 0 := by
      intro h0
      have h1 : c16Beta z u fz fu (n * (t * q) * n⁻¹) = 0 := by
        rw [hconj]
        exact h0
      exact htq_good.1 ((c16_beta_zero_conj H hY hQ htqQ).mp h1)
    have hp : ¬ c16Pplus (c16Beta z u fz fu ((n * t * n⁻¹) * q₀)) := by
      intro h0
      have h1 : c16Pplus (c16Beta z u fz fu (n * (t * q) * n⁻¹)) := by
        rw [hconj]
        exact h0
      exact htq_good.2 ((c16_beta_pplus_conj H hY hK hQ htqQ).mp h1)
    exact ⟨hz, hp⟩
  have hβadd : c16Beta z u fz fu ((n * t * n⁻¹) * q₀)
      = c16Beta z u fz fu (n * t * n⁻¹) + w := by
    rw [c16_beta_add H ht₁Q hq₀Q, hq₀β]
  rw [hβadd] at hgood'
  exact hgood'

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
