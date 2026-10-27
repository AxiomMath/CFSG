module

public import CFSG.ClassicalGroups.UnitaryFlag.WittBasis

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups

variable {p f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem hermitian_nonisotropic_vector (h : UnitaryFieldData p f K) [Nontrivial V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft) :
    ∃ v : V, B v v ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have hpol := sesq_eq_zero_of_forall_isotropic hB hc₀ LinearMap.id hall
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact hx (hBl x fun y => hpol x y)

theorem span_isotropic_eq_top (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : 2 ≤ Module.finrank K V) : Submodule.span K {v : V | v ≠ 0 ∧ B v v = 0} = ⊤ := by
  obtain ⟨⟨w, hw⟩, -, -, -⟩ := hermitian_witt_basis h hB hBl (n := Module.finrank K V) rfl
  have hr : 0 < Module.finrank K V / 2 := by omega
  let i₀ : Fin (Module.finrank K V / 2) := ⟨0, hr⟩
  have hiso : ∀ a, B (w a) (w a) = 0 → w a ∈ Submodule.span K {v : V | v ≠ 0 ∧ B v v = 0} :=
    fun a ha => Submodule.subset_span ⟨w.ne_zero a, ha⟩
  rw [eq_top_iff, ← w.span_eq, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  rcases a with i | k | i
  · exact hiso _ (by rw [hw]; simp)
  · obtain ⟨t, ht⟩ := h.traceLin_surjective (-1)
    have ht' : t + h.bar t = -1 := by
      simpa [UnitaryFieldData.trace] using congrArg Subtype.val ht
    set a := w (.inl i₀)
    set b := w (.inr (.inr i₀))
    set z := w (.inr (.inl k))
    have hv : B (a + t • b + z) (a + t • b + z) = 0 := by
      simp only [a, b, z, map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hw, hypGram_inl_inl, hypGram_inl_inr_inl, hypGram_inl_inr_inr,
        hypGram_inr_inl_inl, hypGram_inr_inl_inr_inl, hypGram_inr_inl_inr_inr,
        hypGram_inr_inr_inl, hypGram_inr_inr_inr_inl, hypGram_inr_inr_inr_inr, ↓reduceIte]
      linear_combination ht'
    have hv0 : a + t • b + z ≠ 0 := by
      intro h0
      have hav := congrArg (B a) h0
      simp only [a, b, z, map_add, map_smul, smul_eq_mul, hw, hypGram_inl_inl,
        hypGram_inl_inr_inl, hypGram_inl_inr_inr, ↓reduceIte, map_zero] at hav
      have ht0 : t = 0 := by linear_combination hav
      rw [ht0, map_zero] at ht'
      exact one_ne_zero (by linear_combination ht')
    have hz : z = (a + t • b + z) - a - t • b := by abel
    rw [hz]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.subset_span ⟨hv0, hv⟩)
      (hiso _ (by simp [hw]))) (Submodule.smul_mem _ _ (hiso _ (by simp [hw])))
  · exact hiso _ (by rw [hw]; simp)

theorem separatingLeft_ker_of_nonisotropic (h : UnitaryFieldData p f K)
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft) {u : V}
    (hu : B u u ≠ 0) :
    (B.domRestrict₁₂ (LinearMap.ker (B u)) (LinearMap.ker (B u))).SeparatingLeft := by
  intro x hx
  apply Subtype.ext
  refine hBl x fun v => ?_
  have hmem : v - (B u v / B u u) • u ∈ LinearMap.ker (B u) := by
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hu, sub_self]
  have h1 := hx ⟨_, hmem⟩
  have hxu : B x u = 0 := by
    rw [← hB.eq u x, show B u x = 0 from x.2, map_zero]
  rw [LinearMap.domRestrict₁₂_apply, map_sub, map_smul, smul_eq_mul, hxu, mul_zero,
    sub_zero] at h1
  exact h1

theorem isotropic_vectors_span (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : 2 ≤ Module.finrank K V) :
    Submodule.span K {v : V | v ≠ 0 ∧ B v v = 0} = ⊤ ∧
      ∀ u : V, B u u ≠ 0 → 3 ≤ Module.finrank K V →
        Submodule.span K {v : V | v ∈ LinearMap.ker (B u) ∧ B v v = 0} =
          LinearMap.ker (B u) := by
  refine ⟨span_isotropic_eq_top h hB hBl hn, fun u hu hn3 => ?_⟩
  have hsurj : Function.Surjective (B u) := by
    intro c
    exact ⟨(c / B u u) • u, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hu]⟩
  have hdim : Module.finrank K (LinearMap.ker (B u)) = Module.finrank K V - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker (B u)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at this
    omega
  have hspan := span_isotropic_eq_top h (hB.domRestrict (LinearMap.ker (B u)))
    (separatingLeft_ker_of_nonisotropic h hB hBl hu) (by omega)
  apply le_antisymm
  · rw [Submodule.span_le]
    exact fun v hv => hv.1
  · intro x hx
    have hx' : (⟨x, hx⟩ : LinearMap.ker (B u)) ∈ Submodule.span K
        {v : LinearMap.ker (B u) |
          v ≠ 0 ∧ (B.domRestrict₁₂ (LinearMap.ker (B u)) (LinearMap.ker (B u))) v v = 0} := by
      rw [hspan]
      trivial
    have hmap := Submodule.mem_map_of_mem (f := (LinearMap.ker (B u)).subtype) hx'
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v.2, hv.2⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
