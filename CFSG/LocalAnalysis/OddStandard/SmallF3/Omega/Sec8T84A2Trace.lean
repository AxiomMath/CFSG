module

public import Mathlib.LinearAlgebra.Trace

import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.OddStandard.SmallF3.Omega

private lemma zmod2_add_add_self {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] (a b : A) :
    (a + b) + b = a := by
  rw [add_assoc, ZModModule.add_self, add_zero]

private lemma zmod2_add_add_add_add_self {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (a b c : A) : (((a + b) + c) + b) + c = a := by
  calc (((a + b) + c) + b) + c
      = ((a + b) + c) + (b + c) := add_assoc _ _ _
    _ = ((a + b) + c) + (c + b) := by rw [add_comm b c]
    _ = (a + b) + b := ZModModule.add_add_add_cancel (a + b) c b
    _ = a := zmod2_add_add_self a b

theorem sec8t84a2_trace_split {M V : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (hV : Even (Module.finrank (ZMod 2) V)) {X : Type*}
    (σ : X → M ≃ₗ[ZMod 2] M) (ρ : X → V ≃ₗ[ZMod 2] V)
    (t : M) (ht : t ≠ 0) (π : M →ₗ[ZMod 2] V) (hπ : Function.Surjective π)
    (hker : ∀ m, π m = 0 → m = 0 ∨ m = t)
    (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] V) (halt : ∀ m, β m m = 0) (hβt : ∀ m, β m t = π m)
    (hσt : ∀ x, σ x t = t) (hπσ : ∀ x m, π (σ x m) = ρ x (π m))
    (hβσ : ∀ x m m', β (σ x m) (σ x m') = ρ x (β m m')) :
    ∃ L : Submodule (ZMod 2) M, IsCompl (Submodule.span (ZMod 2) {t}) L ∧
      ∀ x, ∀ m ∈ L, σ x m ∈ L := by
  have hβt' : ∀ m, β t m = π m := by
    intro m
    have h := halt (m + t)
    simp only [map_add, LinearMap.add_apply, halt, hβt m, zero_add, add_zero] at h
    have h2 : β t m = - π m := eq_neg_of_add_eq_zero_left h
    rwa [ZModModule.neg_eq_self] at h2
  have hπt : π t = 0 := by
    rw [← hβt t, halt t]
  have hker_e : LinearMap.ker (LinearMap.toSpanSingleton (ZMod 2) M t) = ⊥ :=
    LinearMap.ker_toSpanSingleton (R := ZMod 2) ht
  obtain ⟨e, he⟩ := LinearMap.exists_leftInverse_of_injective
    (LinearMap.toSpanSingleton (ZMod 2) M t) hker_e
  have het : e t = 1 := by
    have h1 := LinearMap.ext_iff.mp he (1 : ZMod 2)
    simpa [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply] using h1
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hs_apply : ∀ v, π (s v) = v := fun v => by
    have := LinearMap.ext_iff.mp hs v
    simpa [LinearMap.comp_apply] using this
  let D : X → V →ₗ[ZMod 2] M :=
    fun x => (σ x).toLinearMap.comp s - s.comp (ρ x).toLinearMap
  have hDker : ∀ x v, π (D x v) = 0 := by
    intro x v
    have hDv : D x v = σ x (s v) - s (ρ x v) := by simp [D]
    rw [hDv, map_sub, hπσ x (s v), hs_apply v, hs_apply (ρ x v), sub_self]
  let c : X → V →ₗ[ZMod 2] (ZMod 2) := fun x => e.comp (D x)
  have hD_eq : ∀ x v, D x v = c x v • t := by
    intro x v
    rcases hker (D x v) (hDker x v) with h | h
    · rw [h]; simp [c, h]
    · rw [h]; simp [c, h, het]
  have hσs : ∀ x v, σ x (s v) = s (ρ x v) + c x v • t := by
    intro x v
    have hsub : σ x (s v) - s (ρ x v) = c x v • t := by
      have := hD_eq x v
      simpa [D] using this
    calc σ x (s v) = (σ x (s v) - s (ρ x v)) + s (ρ x v) := (sub_add_cancel _ _).symm
      _ = c x v • t + s (ρ x v) := by rw [hsub]
      _ = s (ρ x v) + c x v • t := add_comm _ _
  let γ : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V := β.compl₁₂ s s
  have hE1 : ∀ x v w, γ (ρ x v) (ρ x w) =
      ρ x (γ v w) + c x w • (ρ x v) + c x v • (ρ x w) := by
    intro x v w
    change β (s (ρ x v)) (s (ρ x w)) =
      ρ x (β (s v) (s w)) + c x w • (ρ x v) + c x v • (ρ x w)
    have h := hβσ x (s v) (s w)
    rw [hσs x v, hσs x w] at h
    have hexp : (β (s (ρ x v)) (s (ρ x w)) + c x w • (ρ x v)) + c x v • (ρ x w)
        = ρ x (β (s v) (s w)) := by
      have h' := h
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_smul,
        hβt, hβt', halt, hs_apply, hπt, smul_zero, add_zero, zero_add] at h'
      convert h' using 1 <;> abel
    rw [eq_comm, ← hexp]
    exact zmod2_add_add_add_add_self
      (β (s (ρ x v)) (s (ρ x w))) (c x w • (ρ x v)) (c x v • (ρ x w))
  have hfin : (Module.finrank (ZMod 2) V : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hV
  let φ : V →ₗ[ZMod 2] (ZMod 2) := (LinearMap.trace (ZMod 2) V).comp γ
  have hφ : ∀ x v, φ (ρ x v) = φ v + c x v := by
    intro x v
    change LinearMap.trace (ZMod 2) V (γ (ρ x v)) =
      LinearMap.trace (ZMod 2) V (γ v) + c x v
    have hE : γ (ρ x v) = (ρ x).conj (γ v) +
        (c x ∘ₗ (ρ x).symm.toLinearMap).smulRight (ρ x v) +
        (c x v) • (LinearMap.id : V →ₗ[ZMod 2] V) := by
      ext w
      simp only [LinearMap.add_apply, LinearEquiv.conj_apply_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.id_apply]
      have h1 := hE1 x v ((ρ x).symm w)
      rw [LinearEquiv.apply_symm_apply] at h1
      exact h1
    have htr := congrArg (LinearMap.trace (ZMod 2) V) hE
    simp only [map_add, map_smul, LinearMap.trace_conj', LinearMap.trace_smulRight,
      LinearMap.trace_id, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at htr
    rw [hfin, smul_zero, add_zero] at htr
    exact htr
  let s' : V →ₗ[ZMod 2] M := s + φ.smulRight t
  have hs'_apply : ∀ v, s' v = s v + φ v • t := by
    intro v; simp [s', LinearMap.smulRight_apply]
  have hπs' : ∀ v, π (s' v) = v := by
    intro v
    rw [hs'_apply, map_add, hs_apply v, map_smul, hπt, smul_zero, add_zero]
  have hσs' : ∀ x v, σ x (s' v) = s' (ρ x v) := by
    intro x v
    rw [hs'_apply, map_add, hσs x v, map_smul, hσt, hs'_apply, hφ x v, add_smul]
    abel
  refine ⟨LinearMap.range s', ?_, ?_⟩
  · refine isCompl_iff.mpr ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro m hm hL
      rw [Submodule.mem_span_singleton] at hm
      obtain ⟨a, ha⟩ := hm
      rw [LinearMap.mem_range] at hL
      obtain ⟨v, hv⟩ := hL
      have hv0 : v = 0 := by
        have h1 : π (a • t) = π (s' v) := by rw [ha, hv]
        rw [map_smul, hπt, smul_zero, hπs' v] at h1
        exact h1.symm
      rw [hv0] at hv
      rw [← hv, map_zero]
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro z
      refine ⟨z - s' (π z), s' (π z), ?_, ?_, ?_⟩
      · rw [Submodule.mem_span_singleton]
        have hz : π (z - s' (π z)) = 0 := by
          rw [map_sub, hπs' (π z), sub_self]
        rcases hker (z - s' (π z)) hz with h | h
        · exact ⟨0, by rw [h, zero_smul]⟩
        · exact ⟨1, by rw [h, one_smul]⟩
      · exact ⟨π z, rfl⟩
      · exact sub_add_cancel z (s' (π z))
  · intro x m hm
    rw [LinearMap.mem_range] at hm
    obtain ⟨v, rfl⟩ := hm
    rw [hσs' x v]
    exact LinearMap.mem_range.mpr ⟨ρ x v, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
