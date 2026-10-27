module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryNorm

public section

namespace CFSG.ComponentClassification.CatalogueBHermitian

noncomputable section

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {sigma : K ≃+* K} (h : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K)

theorem add_left (x x' y : V) : h (x + x') y = h x y + h x' y := by
  rw [map_add, LinearMap.add_apply]

theorem smul_left (c : K) (x y : V) : h (c • x) y = sigma c * h x y := by
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  rfl

theorem self_fixed (hsym : h.IsSymm) (x : V) : sigma (h x x) = h x x :=
  hsym.eq x x

theorem polarization (hne : sigma ≠ 1)
    (S : Submodule K V) (hS : ∀ x ∈ S, h x x = 0)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) : h x y = 0 := by
  obtain ⟨c, hc⟩ := CatalogueBUnitaryNorm.exists_not_fixed sigma hne
  have h1 := hS (x + y) (S.add_mem hx hy)
  have h2 := hS (x + c • y) (S.add_mem hx (S.smul_mem c hy))
  simp only [add_left h] at h1 h2
  simp only [map_add] at h1 h2
  simp only [smul_left h] at h2
  simp only [map_smul, smul_eq_mul, hS x hx, hS y hy] at h1 h2
  have h3 : (c - sigma c) * h x y = 0 := by
    linear_combination h2 - sigma c * h1
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hc.symm)

theorem exists_self_ne_zero [Nontrivial V]
    (hnd : h.Nondegenerate) (hne : sigma ≠ 1) : ∃ x : V, h x x ≠ 0 := by
  by_contra! hd
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  apply hx
  apply hnd.1 x
  intro y
  exact polarization h hne ⊤ (fun z _ => hd z) (by trivial) (by trivial)

theorem exists_smul_unit [Finite K] (hsym : h.IsSymm)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) {x : V} (hx : h x x ≠ 0) :
    ∃ c : K, h (c • x) (c • x) = 1 := by
  obtain ⟨c, hc⟩ := CatalogueBUnitaryNorm.exists_norm sigma hsigma hne (h x x)⁻¹
    (by rw [map_inv₀, self_fixed h hsym]) (inv_ne_zero hx)
  refine ⟨c, ?_⟩
  rw [smul_left, map_smul, smul_eq_mul]
  rw [← mul_assoc, hc, inv_mul_cancel₀ hx]

theorem exists_unit_vector [Finite K] [Nontrivial V] (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    ∃ e : V, h e e = 1 := by
  obtain ⟨x, hx⟩ := exists_self_ne_zero h hnd hne
  obtain ⟨c, hc⟩ := exists_smul_unit h hsym hsigma hne hx
  exact ⟨c • x, hc⟩

theorem unit_vector_ne_zero {e : V} (he : h e e = 1) : e ≠ 0 := by
  intro he0
  have hz : h e e = 0 := by simp only [he0, map_zero]
  exact zero_ne_one (hz.symm.trans he)

@[expose] def orthogonalProjection (e : V) : V →ₗ[K] V :=
  LinearMap.id - (h e).smulRight e

theorem orthogonalProjection_apply (e x : V) :
    orthogonalProjection h e x = x - h e x • e := rfl

theorem orthogonalProjection_mem_ker {e : V} (he : h e e = 1) (x : V) :
    orthogonalProjection h e x ∈ LinearMap.ker (h e) := by
  change h e (x - h e x • e) = 0
  rw [map_sub, map_smul, smul_eq_mul, he, mul_one, sub_self]

theorem vector_decomposition (e x : V) :
    x = h e x • e + orthogonalProjection h e x := by
  rw [orthogonalProjection_apply]
  abel

theorem coefficient_zero {e : V} (he : h e e = 1)
    (c : K) (x : V) (hx : x ∈ LinearMap.ker (h e)) (heq : c • e + x = 0) : c = 0 := by
  have hz := congrArg (h e) heq
  change h e x = 0 at hx
  simpa only [map_add, map_smul, smul_eq_mul, he, mul_one, hx, add_zero, map_zero] using hz

theorem complement_isSymm (hsym : h.IsSymm) (e : V) :
    (h.domRestrict₁₂ (LinearMap.ker (h e)) (LinearMap.ker (h e))).IsSymm :=
  hsym.domRestrict _

theorem complement_nondegenerate (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    {e : V} (he : h e e = 1) :
    (h.domRestrict₁₂ (LinearMap.ker (h e)) (LinearMap.ker (h e))).Nondegenerate := by
  let W := LinearMap.ker (h e)
  have hleft : (h.domRestrict₁₂ W W).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply hnd.1 (x : V)
    intro y
    have hxe : h (x : V) e = 0 := hsym.isRefl e x x.property
    have hxp : h (x : V) (orthogonalProjection h e y) = 0 :=
      hx ⟨orthogonalProjection h e y, orthogonalProjection_mem_ker h he y⟩
    calc
      h (x : V) y = h (x : V) (h e y • e + orthogonalProjection h e y) :=
        congrArg (h (x : V)) (vector_decomposition h e y)
      _ = 0 := by rw [map_add, map_smul, hxe, smul_zero, hxp, add_zero]
  refine ⟨hleft, ?_⟩
  intro x hx
  apply hleft x
  intro y
  exact (complement_isSymm h hsym e).isRefl y x (hx y)

end

end CFSG.ComponentClassification.CatalogueBHermitian
