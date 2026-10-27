module

public import CFSG.ClassicalGroups.Orthogonal.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarKernel

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {σ : K ≃+* K}

instance automorphism_invPair (σ : K ≃+* K) :
    RingHomInvPair σ.toRingHom σ.symm.toRingHom where
  comp_eq := by ext c; exact σ.symm_apply_apply c
  comp_eq₂ := by ext c; exact σ.apply_symm_apply c

instance automorphism_symmInvPair (σ : K ≃+* K) :
    RingHomInvPair σ.symm.toRingHom σ.toRingHom where
  comp_eq := by ext c; exact σ.apply_symm_apply c
  comp_eq₂ := by ext c; exact σ.symm_apply_apply c

@[expose] def FixesSingularLines (Q : QuadraticForm K V) (T : V ≃ₛₗ[σ.toRingHom] V) : Prop :=
  ∀ W : Submodule K V, finrank K W = 1 → (∀ v ∈ W, Q v = 0) →
    W.map T.toLinearMap = W

@[expose] def FixesSingularVectors (Q : QuadraticForm K V)
    (T : V ≃ₛₗ[σ.toRingHom] V) : Prop :=
  ∀ v : V, v ≠ 0 → Q v = 0 → ∃ c : K, T v = c • v

theorem map_span_singleton (T : V ≃ₛₗ[σ.toRingHom] V) (v : V) :
    (Submodule.span K {v}).map T.toLinearMap = Submodule.span K {T v} := by
  rw [Submodule.map_span, Set.image_singleton]
  rfl

theorem fixesSingularLines_iff_vectors (T : V ≃ₛₗ[σ.toRingHom] V) :
    FixesSingularLines Q T ↔ FixesSingularVectors Q T := by
  constructor
  · intro h v hv hQv
    have hs : ∀ x ∈ Submodule.span K {v}, Q x = 0 := by
      intro x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul_eq_sq, hQv, mul_zero]
    have hline := h _ (finrank_span_singleton hv) hs
    have hmem : T v ∈ (Submodule.span K {v}).map T.toLinearMap :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self v)
    rw [hline] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  · intro h W hW hs
    obtain ⟨v, hv, hgen⟩ := finrank_eq_one_iff'.mp hW
    have hv0 : (v : V) ≠ 0 := by
      intro h0
      apply hv
      exact Subtype.ext h0
    obtain ⟨a, ha⟩ := h v hv0 (hs v v.property)
    have ha0 : a ≠ 0 := by
      intro h0
      have hTv : T v = 0 := by rw [ha, h0, zero_smul]
      exact hv0 (T.map_eq_zero_iff.mp hTv)
    have hspan : W = Submodule.span K {(v : V)} := by
      apply le_antisymm
      · intro w hw
        obtain ⟨c, hc⟩ := hgen ⟨w, hw⟩
        exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
      · exact (Submodule.span_singleton_le_iff_mem (v : V) W).mpr v.property
    rw [hspan, map_span_singleton, ha]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 a ha0) (v : V)

theorem coefficient_ne_zero (T : V ≃ₛₗ[σ.toRingHom] V) {v : V} (hv : v ≠ 0)
    {a : K} (ha : T v = a • v) : a ≠ 0 := by
  intro h0
  have hTv : T v = 0 := by rw [ha, h0, zero_smul]
  exact hv (T.map_eq_zero_iff.mp hTv)

theorem polar_similarity (T : V ≃ₛₗ[σ.toRingHom] V) (μ : Kˣ)
    (hT : ∀ v, Q (T v) = (μ : K) * σ (Q v)) (v w : V) :
    polar Q (T v) (T w) = (μ : K) * σ (polar Q v w) := by
  unfold polar
  rw [← map_add T, hT, hT, hT, map_sub, map_sub]
  ring

@[expose] def originalLinearEquiv (T : V ≃ₛₗ[σ.toRingHom] V)
    (hσ : σ = RingEquiv.refl K) : V ≃ₗ[K] V :=
  T.toAddEquiv.toLinearEquiv fun c v => by
    change T (c • v) = c • T v
    rw [T.map_smulₛₗ]
    simp [hσ]

theorem originalLinearEquiv_apply (T : V ≃ₛₗ[σ.toRingHom] V)
    (hσ : σ = RingEquiv.refl K) (v : V) : originalLinearEquiv T hσ v = T v :=
  rfl

theorem originalLinearEquiv_symm_apply (T : V ≃ₛₗ[σ.toRingHom] V)
    (hσ : σ = RingEquiv.refl K) (v : V) : (originalLinearEquiv T hσ).symm v = T.symm v :=
  rfl

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarKernel
