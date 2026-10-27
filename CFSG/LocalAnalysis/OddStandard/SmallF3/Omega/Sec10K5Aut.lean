module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Faith
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Perm

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

namespace SL23Pair

variable {K : Type} [Group K] [Finite K] {A B : Subgroup K} (h : SL23Pair K A B)

include h

theorem embA_mem_pCore {q : SL23} (hq : q ^ 4 = 1) : h.embA q ∈ CFSG.pCore 2 K := by
  let P : Subgroup K := sl23Q8.map h.embA
  have hPn : P.Normal := by
    refine ⟨fun n hn k => ?_⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hn
    obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul k
    obtain ⟨t, rfl⟩ := h.exists_embA ha
    have hb' : b * h.embA s = h.embA s * b := (h.comm _ (h.embA_mem s) b hb).symm
    have e : h.embA t * b * h.embA s * (h.embA t * b)⁻¹ = h.embA (t * s * t⁻¹) := by
      simp only [map_mul, map_inv, mul_inv_rev]
      calc h.embA t * b * h.embA s * (b⁻¹ * (h.embA t)⁻¹)
          = h.embA t * (b * h.embA s) * b⁻¹ * (h.embA t)⁻¹ := by group
        _ = h.embA t * (h.embA s * b) * b⁻¹ * (h.embA t)⁻¹ := by rw [hb']
        _ = h.embA t * h.embA s * (h.embA t)⁻¹ := by group
    rw [e]
    exact Subgroup.mem_map.mpr ⟨t * s * t⁻¹, sl23Q8_normal.conj_mem s hs t, rfl⟩
  have hP2 : IsPGroup 2 P := sl23Q8_isPGroup.map h.embA
  have hle : P ≤ CFSG.pCore 2 K := le_sSup ⟨hPn, hP2⟩
  exact hle (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩)

theorem theta_conj_embA {q : SL23} {v : Equiv.Perm (Fin 4)}
    (hq : ∀ i, q * k5g i * q⁻¹ = k5g (v i) ∨ q * k5g i * q⁻¹ = (k5g (v i))⁻¹) :
    h.theta (MulAut.conj (h.embA q)) = Equiv.Perm.sumCongr v 1 := by
  ext p
  rcases p with i | j
  · have key : MulAut.conj (h.embA q) (h.gen (Sum.inl i)) = h.embA (q * k5g i * q⁻¹) := by
      rw [MulAut.conj_apply, ← h.embA_k5g, map_mul, map_mul, map_inv]
    have hi : h.theta (MulAut.conj (h.embA q)) (Sum.inl i) = Sum.inl (v i) := by
      apply h.theta_eq
      rw [key]
      rcases hq i with e | e
      · left
        rw [e, h.embA_k5g]
      · right
        rw [e, map_inv, h.embA_k5g]
    rw [hi]
    simp
  · have hc : h.embA q * h.gen (Sum.inr j) = h.gen (Sum.inr j) * h.embA q :=
      h.comm _ (h.embA_mem q) _ (h.gen_mem_B j)
    have key : MulAut.conj (h.embA q) (h.gen (Sum.inr j)) = h.gen (Sum.inr j) := by
      rw [MulAut.conj_apply, hc]
      group
    have hj : h.theta (MulAut.conj (h.embA q)) (Sum.inr j) = Sum.inr j :=
      h.theta_eq (Or.inl key)
    rw [hj]
    simp

theorem theta_inl_right {σ : MulAut K} (hσ : ∀ k ∈ A, σ k ∈ B) :
    (h.theta σ (Sum.inl 0)).isLeft = false :=
  h.isLeft_eq_false_of_mem_B (hσ _ (h.gen_mem_A 0)) (h.theta_spec σ (Sum.inl 0))

theorem aut_of_pair (Φ Ψ : Subgroup (MulAut K)) (hΨΦ : Ψ ≤ Φ) (hΦ2 : IsPGroup 2 Φ)
    (hidx : Ψ.relIndex Φ = 2) (hΨ : 64 ≤ Nat.card Ψ)
    (hQ : ∀ q ∈ CFSG.pCore 2 K, MulAut.conj q ∈ Ψ) (hσ : ∃ σ ∈ Ψ, ∀ k ∈ A, σ k ∈ B) :
    ∃ ψ ∈ Φ, ψ ∉ Ψ ∧ ψ * ψ = 1 ∧ (∀ k ∈ A, ψ k ∈ A) ∧ (∀ k ∈ B, ψ k = k) ∧
      ¬ ∃ k ∈ A, ∀ y ∈ A, ψ y = k * y * k⁻¹ := by
  have hinj := h.theta_injective
  haveI : Finite (MulAut K) := Finite.of_injective h.theta hinj
  have hrelmul : Ψ.relIndex Φ * Nat.card Ψ = Nat.card Φ := by
    have := Subgroup.relIndex_mul_card (H := Ψ) (K := Φ)
    rwa [inf_eq_left.mpr hΨΦ] at this
  have hcardΦ : 128 ≤ Nat.card Φ := by
    rw [← hrelmul, hidx]
    omega
  have hne : Ψ ≠ Φ := by
    intro heq
    rw [heq, Subgroup.relIndex_self] at hidx
    omega
  have hcard' : 128 ≤ Nat.card (Φ.map h.theta) := by
    have := Nat.card_congr (Subgroup.equivMapOfInjective Φ h.theta hinj).toEquiv
    rw [← this]
    exact hcardΦ
  have hne' : Ψ.map h.theta ≠ Φ.map h.theta := fun e => hne (Subgroup.map_injective hinj e)
  have hV1 : ∀ v ∈ klein, Equiv.Perm.sumCongr v 1 ∈ Ψ.map h.theta := by
    intro v hv
    obtain ⟨q, hq4, hq⟩ := exists_pow_four_of_klein hv
    exact Subgroup.mem_map.mpr
      ⟨MulAut.conj (h.embA q), hQ _ (h.embA_mem_pCore hq4), h.theta_conj_embA hq⟩
  obtain ⟨σ, hσΨ, hσA⟩ := hσ
  have hσ' : ∃ σ' ∈ Ψ.map h.theta, (σ' (Sum.inl 0)).isLeft = false :=
    ⟨h.theta σ, Subgroup.mem_map.mpr ⟨σ, hσΨ, rfl⟩, h.theta_inl_right hσA⟩
  obtain ⟨τ, hsign, hττ, hτΦ, hτΨ⟩ := lemma_T (Φ.map h.theta) (Ψ.map h.theta)
    (Subgroup.map_mono hΨΦ) (hΦ2.map h.theta) hne' hcard'
    (fun w hw p q hpq => by
      obtain ⟨α, _, rfl⟩ := Subgroup.mem_map.mp hw
      exact h.theta_block α hpq) hV1 hσ'
  obtain ⟨ψ, hψΦ, hψθ⟩ := Subgroup.mem_map.mp hτΦ
  have hl : ∀ i, h.theta ψ (Sum.inl i) = Sum.inl (τ i) := fun i => by rw [hψθ]; simp
  have hr : ∀ j, h.theta ψ (Sum.inr j) = Sum.inr j := fun j => by rw [hψθ]; simp
  refine ⟨ψ, hψΦ, ?_, ?_, ?_, fun k hk => h.fix_B hr hk, ?_⟩
  · intro hψΨ
    exact hτΨ (hψθ ▸ Subgroup.mem_map.mpr ⟨ψ, hψΨ, rfl⟩)
  · apply hinj
    rw [map_mul, hψθ, Equiv.Perm.sumCongr_mul, hττ, mul_one, Equiv.Perm.sumCongr_one, map_one]
  · have hmem : ∀ i, ψ (h.gen (Sum.inl i)) ∈ A := fun i =>
      h.mem_A_of_isLeft (q := h.theta ψ (Sum.inl i)) (by rw [hl i]; rfl) (h.theta_spec ψ _)
    exact fun k hk => h.map_mem_A (hmem 0) (hmem 1) hk
  · rintro ⟨k, hkA, hk⟩
    obtain ⟨s, rfl⟩ := h.exists_embA hkA
    have hact : ∀ i, s * k5g i * s⁻¹ = k5g (τ i) ∨ s * k5g i * s⁻¹ = (k5g (τ i))⁻¹ := by
      intro i
      have e1 : ψ (h.gen (Sum.inl i)) = h.embA (s * k5g i * s⁻¹) := by
        rw [← h.embA_k5g, hk _ (h.embA_mem _), map_mul, map_mul, map_inv]
      have e2 := h.theta_spec ψ (Sum.inl i)
      rw [hl i] at e2
      rcases e2 with e2 | e2
      · left
        apply h.embA_injective
        rw [← e1, e2, h.embA_k5g]
      · right
        apply h.embA_injective
        rw [← e1, e2, map_inv, h.embA_k5g]
    have h1 := sign_of_act hact
    rw [hsign] at h1
    exact absurd h1 (by decide)

end SL23Pair

end CFSG.OddStandard.SmallF3.Omega.K5
