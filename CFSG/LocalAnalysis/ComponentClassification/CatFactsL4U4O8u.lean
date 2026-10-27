module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8a
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

variable {K : Type} [Field K] {b c : K}

theorem conj_fusion_of {G H : Type*} [Group G] [Group H] (θ : G ≃* H) (φ : MulAut G)
    (P : MulAut H) (hφ : ∀ x, θ (φ x) = P (θ x)) (g ζ : G)
    (h : ∀ X, (θ g)⁻¹ * P (θ g * X * (θ g)⁻¹) * θ g = P (θ ζ * X * (θ ζ)⁻¹)) :
    (MulAut.conj g)⁻¹ * φ * MulAut.conj g = φ * MulAut.conj ζ := by
  apply MulEquiv.ext
  intro x
  apply θ.injective
  change θ (g⁻¹ * φ (g * x * g⁻¹) * g) = θ (φ (ζ * x * ζ⁻¹))
  simp only [map_mul θ, map_inv θ]
  rw [hφ, hφ]
  simp only [map_mul θ, map_inv θ]
  exact h (θ x)

theorem quot_fusion (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (μ : Kˣ)
    (hsim : ∀ x, Q8 K b c (A x) = (μ : K) * Q8 K b c x) (γ z : orthogonalDerived (Q8 K b c))
    (hrel : ∀ v, A (γ.val.val v) = γ.val.val (A (z.val.val v)))
    (X : projectiveDerived (Q8 K b c)) :
    (QuotientGroup.mk' ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) γ)⁻¹ *
      projectiveConjugation (Q8 K b c) A μ hsim (QuotientGroup.mk' _ γ * X *
        (QuotientGroup.mk' _ γ)⁻¹) * QuotientGroup.mk' _ γ =
      projectiveConjugation (Q8 K b c) A μ hsim
        (QuotientGroup.mk' _ z * X * (QuotientGroup.mk' _ z)⁻¹) := by
  have hrel' : A * γ.val.val = γ.val.val * A * z.val.val := LinearEquiv.ext hrel
  have hconj : γ.val.val⁻¹ * A * γ.val.val = A * z.val.val := by
    calc γ.val.val⁻¹ * A * γ.val.val = γ.val.val⁻¹ * (A * γ.val.val) := by group
      _ = A * z.val.val := by rw [hrel']; group
  set N := (scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c)) with hN
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N X
  let R := restrictAutomorphism (orthogonalDerived (Q8 K b c))
    (similarityConjugation (Q8 K b c) A μ hsim) (orthogonalDerived_invariant (Q8 K b c) A μ hsim)
  have hP : ∀ a : orthogonalDerived (Q8 K b c),
      projectiveConjugation (Q8 K b c) A μ hsim (QuotientGroup.mk' N a) =
        QuotientGroup.mk' N (R a) := fun a => projectiveConjugation_mk (Q8 K b c) A μ hsim a
  have key : γ⁻¹ * R (γ * w * γ⁻¹) * γ = R (z * w * z⁻¹) := by
    apply Subtype.ext
    apply Subtype.ext
    change γ.val.val⁻¹ * (A * (γ.val.val * w.val.val * γ.val.val⁻¹) * A⁻¹) * γ.val.val =
      A * (z.val.val * w.val.val * z.val.val⁻¹) * A⁻¹
    have e : γ.val.val⁻¹ * (A * (γ.val.val * w.val.val * γ.val.val⁻¹) * A⁻¹) * γ.val.val =
        (γ.val.val⁻¹ * A * γ.val.val) * w.val.val * (γ.val.val⁻¹ * A * γ.val.val)⁻¹ := by group
    rw [e, hconj]
    group
  calc (QuotientGroup.mk' N γ)⁻¹ * projectiveConjugation (Q8 K b c) A μ hsim
        (QuotientGroup.mk' N γ * QuotientGroup.mk' N w * (QuotientGroup.mk' N γ)⁻¹) *
        QuotientGroup.mk' N γ =
        (QuotientGroup.mk' N γ)⁻¹ * projectiveConjugation (Q8 K b c) A μ hsim
          (QuotientGroup.mk' N (γ * w * γ⁻¹)) * QuotientGroup.mk' N γ := rfl
    _ = (QuotientGroup.mk' N γ)⁻¹ * QuotientGroup.mk' N (R (γ * w * γ⁻¹)) *
          QuotientGroup.mk' N γ :=
        congrArg (fun t => (QuotientGroup.mk' N γ)⁻¹ * t * QuotientGroup.mk' N γ) (hP _)
    _ = QuotientGroup.mk' N (γ⁻¹ * R (γ * w * γ⁻¹) * γ) := rfl
    _ = QuotientGroup.mk' N (R (z * w * z⁻¹)) := congrArg (QuotientGroup.mk' N) key
    _ = projectiveConjugation (Q8 K b c) A μ hsim (QuotientGroup.mk' N (z * w * z⁻¹)) :=
        (hP _).symm

theorem fusion_of_comm (hQ0 : ∃ v, Q8 K b c v ≠ 0) (φ : MulAut (G0 K b c))
    (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (μ : Kˣ)
    (hsim : ∀ x, Q8 K b c (A x) = (μ : K) * Q8 K b c x)
    (hφ : ∀ x, theta K b c hQ0 (φ x) =
      projectiveConjugation (Q8 K b c) A μ hsim (theta K b c hQ0 x))
    (γ z : orthogonalDerived (Q8 K b c))
    (hrel : ∀ v, A (γ.val.val v) = γ.val.val (A (z.val.val v))) :
    (MulAut.conj ((theta K b c hQ0).symm (QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) γ)))⁻¹ * φ *
      MulAut.conj ((theta K b c hQ0).symm (QuotientGroup.mk' _ γ)) =
      φ * MulAut.conj ((theta K b c hQ0).symm (QuotientGroup.mk' _ z)) := by
  refine conj_fusion_of (theta K b c hQ0) φ (projectiveConjugation (Q8 K b c) A μ hsim) hφ _ _
    fun X => ?_
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact quot_fusion A μ hsim γ z hrel X

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
