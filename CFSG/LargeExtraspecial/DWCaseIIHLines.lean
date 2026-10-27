module

public import CFSG.LargeExtraspecial.DWCaseIIHAlt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule CFSG.GroupTheory.GLnTwoSplitting

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_linearMap_step (e : V → V)
    (he : ∀ u v, e (u + v) + e u + e v ∈ span (ZMod 2) {u, v}) {W : Submodule (ZMod 2) V}
    (hW : ∀ u ∈ W, e u ∈ span (ZMod 2) {u}) {b : V} (hb : b ∉ W) :
    ∃ w : Module.End (ZMod 2) V, ∀ v ∈ (ZMod 2) ∙ b ⊔ W, w v + e v ∈ span (ZMod 2) {v} := by
  obtain ⟨f, hfb, hfW⟩ := exists_le_ker_of_notMem hb
  have hfb1 : f b = 1 := by
    rcases zmod_two_eq_zero_or_one (f b) with h | h
    · exact absurd h hfb
    · exact h
  have hfW' : ∀ u ∈ W, f u = 0 := fun u hu => hfW hu
  have hb0 : b ≠ 0 := fun h => hb (h ▸ W.zero_mem)
  let R : V → ZMod 2 → Prop := fun u μ => e (u + b) + e b + μ • b ∈ span (ZMod 2) {u + b}
  have hex : ∀ u ∈ W, ∃ μ, R u μ := by
    intro u hu
    obtain ⟨c, hc⟩ := mem_span_singleton.mp (hW u hu)
    have h3 : e u ∈ span (ZMod 2) {u, b} := hc ▸ smul_mem _ _ (subset_span (by simp))
    obtain ⟨a, c', hac⟩ := mem_span_pair.mp (add_mem (he u b) h3)
    refine ⟨a + c', mem_span_singleton.mpr ⟨a, ?_⟩⟩
    have h4 : e (u + b) + e b = e (u + b) + e u + e b + e u := by abel_two
    rw [h4, ← hac]
    zmod_two_module
  have huniq : ∀ u, u ≠ 0 → ∀ μ μ', R u μ → R u μ' → μ = μ' := by
    intro u hu0 μ μ' h h'
    have h2 : (μ + μ') • b ∈ span (ZMod 2) {u + b} := by
      have h3 := add_mem h h'
      convert h3 using 1
      zmod_two_module
    by_contra hne
    have hne' : μ + μ' = 1 := by
      rcases zmod_two_eq_zero_or_one (μ + μ') with h0 | h0
      · exact absurd (zmod_two_eq_of_add_eq_zero h0) hne
      · exact h0
    rw [hne', one_smul] at h2
    rcases mem_span_singleton_iff_zmod_two.mp h2 with h0 | h0
    · exact hb0 h0
    · exact hu0 (by
        have h5 : u = u + b + b := by abel_two
        rw [h5, ← h0]
        abel_two)
  have hkey : ∀ u ∈ W, ∀ u' ∈ W, u ≠ 0 → u' ≠ 0 → u ≠ u' → ∀ μ μ'', R u μ → R (u + u') μ'' →
      μ = μ'' := by
    intro u hu u' hu' hu0 hu'0 huu' μ μ'' h h''
    obtain ⟨c, hc⟩ := mem_span_singleton.mp h
    obtain ⟨c'', hc''⟩ := mem_span_singleton.mp h''
    obtain ⟨p, r, hpr⟩ := mem_span_pair.mp (he (u + b) u')
    obtain ⟨r', hr'⟩ := mem_span_singleton.mp (hW u' hu')
    rw [add_right_comm u u' b] at hc''
    have hcomb : (c'' + c + p) • u + (c'' + r' + r) • u' + (c'' + μ'' + c + μ + p) • b = 0 := by
      linear_combination (norm := zmod_two_module) hc'' + hc + hpr + hr'
    have hf := congrArg f hcomb
    simp only [map_add, map_smul, hfW' u hu, hfW' u' hu', hfb1, smul_eq_mul, mul_zero, mul_one,
      zero_add, map_zero] at hf
    rw [hf, zero_smul, add_zero] at hcomb
    obtain ⟨h1, -⟩ := eq_zero_of_smul_add_smul_eq_zero hu0 hu'0 huu' hcomb
    linear_combination (norm := (ring_nf; reduce_mod_char)) hf - h1
  have hconst : ∀ u₁ ∈ W, ∀ u₂ ∈ W, u₁ ≠ 0 → u₂ ≠ 0 → ∀ μ₁ μ₂, R u₁ μ₁ → R u₂ μ₂ →
      μ₁ = μ₂ := by
    intro u₁ h₁ u₂ h₂ h10 h20 μ₁ μ₂ r1 r2
    by_cases h12 : u₁ = u₂
    · subst h12
      exact huniq u₁ h10 μ₁ μ₂ r1 r2
    · have hu' : u₁ + u₂ ≠ 0 := fun h => h12 (vec_eq_of_add_eq_zero h)
      have hne : u₁ ≠ u₁ + u₂ := fun h => h20 (by
        have h5 : u₂ = u₁ + (u₁ + u₂) := by abel_two
        rw [h5, ← h, ZModModule.add_self])
      have h5 : u₁ + (u₁ + u₂) = u₂ := by abel_two
      exact hkey u₁ h₁ (u₁ + u₂) (add_mem h₁ h₂) h10 hu' hne μ₁ μ₂ r1 (by rwa [h5])
  have hR0 : ∀ μ, R 0 μ := fun μ => by
    change e (0 + b) + e b + μ • b ∈ span (ZMod 2) {0 + b}
    rw [zero_add, ZModModule.add_self, zero_add]
    exact smul_mem _ _ (mem_span_singleton_self b)
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, ∀ u ∈ W, R u μ₀ := by
    by_cases hW0 : ∃ u₀ ∈ W, u₀ ≠ 0
    · obtain ⟨u₀, hu₀, hu₀0⟩ := hW0
      obtain ⟨μ₀, h₀⟩ := hex u₀ hu₀
      refine ⟨μ₀, fun u hu => ?_⟩
      by_cases hu0 : u = 0
      · rw [hu0]
        exact hR0 μ₀
      · obtain ⟨μ, hμ⟩ := hex u hu
        rwa [hconst u₀ hu₀ u hu hu₀0 hu0 μ₀ μ h₀ hμ]
    · push Not at hW0
      exact ⟨0, fun u hu => (hW0 u hu) ▸ hR0 0⟩
  refine ⟨f.smulRight (e b + μ₀ • b), fun v hv => ?_⟩
  obtain ⟨y, hy, u, hu, rfl⟩ := mem_sup.mp hv
  obtain ⟨c, rfl⟩ := mem_span_singleton.mp hy
  rcases zmod_two_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul, zero_add, LinearMap.smulRight_apply, hfW' u hu, zero_smul, zero_add]
    exact hW u hu
  · rw [one_smul, LinearMap.smulRight_apply, map_add, hfb1, hfW' u hu, add_zero, one_smul,
      add_comm b u]
    have h5 := hμ₀ u hu
    convert h5 using 1
    abel

theorem exists_linearMap_add_mem_span [FiniteDimensional (ZMod 2) V] (e : V → V)
    (he0 : e 0 = 0) (he : ∀ u v, e (u + v) + e u + e v ∈ span (ZMod 2) {u, v}) :
    ∃ w : Module.End (ZMod 2) V, ∀ v, w v + e v ∈ span (ZMod 2) {v} := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype V := Fintype.ofFinite V
  suffices key : ∀ s : Finset V, ∃ w : Module.End (ZMod 2) V,
      ∀ v ∈ span (ZMod 2) (s : Set V), w v + e v ∈ span (ZMod 2) {v} by
    obtain ⟨w, hw⟩ := key Finset.univ
    exact ⟨w, fun v => hw v (subset_span (by simp))⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, fun v hv => ?_⟩
    rw [Finset.coe_empty, span_empty, mem_bot] at hv
    rw [hv, he0, map_zero, add_zero]
    exact zero_mem _
  | insert b s _ ih =>
    obtain ⟨w, hw⟩ := ih
    rw [Finset.coe_insert, span_insert]
    by_cases hb : b ∈ span (ZMod 2) (s : Set V)
    · refine ⟨w, fun v hv => hw v ?_⟩
      rwa [sup_eq_right.mpr ((span_singleton_le_iff_mem _ _).mpr hb)] at hv
    · have he' : ∀ u v, (e (u + v) + w (u + v)) + (e u + w u) + (e v + w v) ∈
          span (ZMod 2) {u, v} := by
        intro u v
        have h5 : (e (u + v) + w (u + v)) + (e u + w u) + (e v + w v) =
            e (u + v) + e u + e v := by
          rw [map_add]
          abel_two
        rw [h5]
        exact he u v
      obtain ⟨w', hw'⟩ := exists_linearMap_step (fun v => e v + w v) he'
        (W := span (ZMod 2) (s : Set V))
        (fun u hu => by rw [add_comm]; exact hw u hu) hb
      refine ⟨w' + w, fun v hv => ?_⟩
      have h5 := hw' v hv
      rw [LinearMap.add_apply, add_assoc, add_comm (w v)]
      exact h5

end CFSG.LargeExtraspecial.DW
