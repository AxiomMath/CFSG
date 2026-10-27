module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

theorem exists_conj_of_sylow {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    {T₀ : Subgroup K} (hp : IsPGroup p T₀) (hidx : ¬ p ∣ T₀.index) (T : Sylow p K) :
    ∃ g : K, ∀ t : K, t ∈ (T : Subgroup K) ↔ g⁻¹ * t * g ∈ T₀ := by
  let S₀ : Sylow p K := hp.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S₀ T
  refine ⟨g, fun t => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, hst⟩
    have : g⁻¹ * t * g = s := by
      rw [← hst]
      simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hs
  · intro ht
    refine ⟨g⁻¹ * t * g, ht, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]

theorem conj_mem_normalizer {K : Type*} [Group K] {T T₀ : Subgroup K} {g : K}
    (hT : ∀ t : K, t ∈ T ↔ g⁻¹ * t * g ∈ T₀) {n : K} (hn : n ∈ normalizer (T₀ : Set K)) :
    g * n * g⁻¹ ∈ normalizer (T : Set K) := by
  rw [mem_normalizer_iff] at hn ⊢
  intro x
  rw [hT x, hT (g * n * g⁻¹ * x * (g * n * g⁻¹)⁻¹)]
  have := hn (g⁻¹ * x * g)
  simpa [mul_assoc] using this

theorem relIndex_normalizer_modEq_one {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (T : Sylow p K) {Y : Subgroup K} (hY : normalizer ((T : Subgroup K) : Set K) ≤ Y) :
    (normalizer ((T : Subgroup K) : Set K)).relIndex Y ≡ 1 [MOD p] := by
  have hTY : (T : Subgroup K) ≤ Y := le_normalizer.trans hY
  have h1 := card_sylow_modEq_one p Y
  rw [(T.subtype hTY).card_eq_index_normalizer] at h1
  have h2 : normalizer ((T.subtype hTY : Sylow p Y) : Set Y) =
      (normalizer ((T : Subgroup K) : Set K)).subgroupOf Y := by
    rw [← Sylow.coe_coe, Sylow.coe_subtype, ← subgroupOf_normalizer_eq hTY]
  rw [h2] at h1
  exact h1

theorem index_normalizer_eq_mul {K : Type*} [Group K] {T : Subgroup K} {Y : Subgroup K}
    (hY : normalizer (T : Set K) ≤ Y) :
    (normalizer (T : Set K)).index = (normalizer (T : Set K)).relIndex Y * Y.index :=
  (relIndex_mul_index hY).symm

theorem eq_normalizer_or_top_of_index {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (T : Sylow p K) {n : ℕ} (hn : (normalizer ((T : Subgroup K) : Set K)).index = n)
    (hfac : ∀ m d : ℕ, m * d = n → m ≡ 1 [MOD p] → m = 1 ∨ d = 1)
    {Y : Subgroup K} (hY : normalizer ((T : Subgroup K) : Set K) ≤ Y) :
    Y = normalizer ((T : Subgroup K) : Set K) ∨ Y = ⊤ := by
  have hmul := index_normalizer_eq_mul (T := (T : Subgroup K)) hY
  have hmod := relIndex_normalizer_modEq_one T hY
  rcases hfac _ _ (hmul.symm.trans hn) hmod with h | h
  · left
    exact le_antisymm (relIndex_eq_one.mp h) hY
  · right
    exact index_eq_one.mp h

end CFSG.LocalAnalysis.RankThreeTheoremC
