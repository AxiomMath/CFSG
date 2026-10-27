module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}

omit [FiniteDimensional K N] in
theorem exists_notMem_pair_of_not_le {W U₁ U₂ : Submodule K N} (h₁ : ¬ W ≤ U₁)
    (h₂ : ¬ W ≤ U₂) : ∃ z ∈ W, z ∉ U₁ ∧ z ∉ U₂ := by
  obtain ⟨u, hu, hu₁⟩ := SetLike.not_le_iff_exists.mp h₁
  obtain ⟨v, hv, hv₂⟩ := SetLike.not_le_iff_exists.mp h₂
  by_cases hu₂ : u ∈ U₂
  · by_cases hv₁ : v ∈ U₁
    · refine ⟨u + v, W.add_mem hu hv, fun h => hu₁ ?_, fun h => hv₂ ?_⟩
      · simpa using U₁.sub_mem h hv₁
      · simpa using U₂.sub_mem h hu₂
    · exact ⟨v, hv, hv₁, hv₂⟩
  · exact ⟨u, hu, hu₁, hu₂⟩

theorem exists_perp_form_ne_zero_of_notMem_span (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    {y y' a : N} (ha : a ∉ Submodule.span K ({y, y'} : Set N)) :
    ∃ z : N, BN y z = 0 ∧ BN y' z = 0 ∧ BN z a ≠ 0 := by
  by_contra hcon
  apply ha
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hBNnd hBN.isRefl (Submodule.span K {y, y'}),
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hn
  by_contra hna
  exact hcon ⟨n, hn y (Submodule.subset_span (by simp)), hn y' (Submodule.subset_span (by simp)),
    hna⟩

theorem exists_orth_path (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) (hdim : 4 ≤ finrank K N)
    {a x x' : N} (hx : BN x a ≠ 0) (hx' : BN x' a ≠ 0) :
    ∃ z₁ z₂ : N, BN x z₁ = 0 ∧ BN z₁ z₂ = 0 ∧ BN z₂ x' = 0 ∧ BN z₁ a ≠ 0 ∧ BN z₂ a ≠ 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  have hxmem : x ∈ Submodule.span K ({x, x'} : Set N) := Submodule.subset_span (by simp)
  have hx'mem : x' ∈ Submodule.span K ({x, x'} : Set N) := Submodule.subset_span (by simp)
  by_cases hA : a ∈ Submodule.span K ({x, x'} : Set N)
  ·
    have hWU₁ : ¬ BN.orthogonal (Submodule.span K {x}) ≤
        BN.orthogonal (Submodule.span K {a}) := by
      intro hle
      have h1 := LinearMap.BilinForm.orthogonal_le (B := BN) hle
      rw [LinearMap.BilinForm.orthogonal_orthogonal hBNnd hBN.isRefl,
        LinearMap.BilinForm.orthogonal_orthogonal hBNnd hBN.isRefl] at h1
      obtain ⟨s, hs⟩ :=
        Submodule.mem_span_singleton.mp (h1 (Submodule.mem_span_singleton_self a))
      apply hx
      rw [← hs, map_smul, hBN.self_eq_zero, smul_zero]
    have hWU₂ : ¬ BN.orthogonal (Submodule.span K {x}) ≤
        Submodule.span K ({x, x'} : Set N) := by
      intro hle
      have h1 := Submodule.finrank_mono hle
      rw [LinearMap.BilinForm.finrank_orthogonal hBNnd, finrank_span_singleton hx0] at h1
      have h2 : finrank K (Submodule.span K ({x, x'} : Set N)) ≤ 2 := by
        classical
        have h := finrank_span_finset_le_card (R := K) ({x, x'} : Finset N)
        rw [Finset.coe_pair] at h
        exact h.trans Finset.card_le_two
      omega
    obtain ⟨z₁, hz₁W, hz₁U₁, hz₁U₂⟩ := exists_notMem_pair_of_not_le hWU₁ hWU₂
    have hxz₁ : BN x z₁ = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hz₁W) x (Submodule.mem_span_singleton_self x)
    have hz₁a : BN z₁ a ≠ 0 := by
      intro h
      apply hz₁U₁
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hn
      have h' : BN a z₁ = 0 := hBN.eq_iff.mp h
      simp [h']
    have hz₁x'a : a ∉ Submodule.span K ({z₁, x'} : Set N) := by
      intro h
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp h
      obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.mp hA
      have hα : α ≠ 0 := by
        rintro rfl
        apply hx'
        rw [← hαβ]
        simp [hBN.self_eq_zero]
      apply hz₁U₂
      have key : α • z₁ = γ • x + (δ - β) • x' := by
        have h1 : α • z₁ = a - β • x' := eq_sub_of_add_eq hαβ
        rw [h1, ← hγδ, sub_smul]
        abel
      have hz : z₁ = α⁻¹ • (γ • x + (δ - β) • x') := by
        rw [← key, inv_smul_smul₀ hα]
      rw [hz]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hxmem)
        (Submodule.smul_mem _ _ hx'mem))
    obtain ⟨z₂, hz₂, hz₂x', hz₂a⟩ := exists_perp_form_ne_zero_of_notMem_span hBN hBNnd hz₁x'a
    exact ⟨z₁, z₂, hxz₁, hz₂, hBN.eq_iff.mpr hz₂x', hz₁a, hz₂a⟩
  ·
    obtain ⟨z, hxz, hx'z, hza⟩ := exists_perp_form_ne_zero_of_notMem_span hBN hBNnd hA
    exact ⟨z, z, hxz, hBN.self_eq_zero z, hBN.eq_iff.mpr hx'z, hza, hza⟩

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
