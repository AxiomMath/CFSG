module

public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open CFSG.ClassicalGroups.Alternating
open Matrix
open LinearMap (BilinForm)

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

theorem additive_eq_zero_of_form_eq_zero {A : Type*} [AddGroup A] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) (g : V →+ A) {x : V}
    (hg : ∀ T : Gsp B, T.app x = x → ∀ z : V, g (T.app z) = g z) {y : V} (hxy : B x y = 0) :
    g y = 0 := by
  by_cases hy : y = 0
  · rw [hy, map_zero]
  obtain ⟨z, hz⟩ : ∃ z, B z y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy (hBn.2 y hcon)
  let T : Gsp B := ⟨symplecticTransvection B hB y (B z y)⁻¹,
    symplecticTransvection_mem_bilinIsometryGroup hB _ _⟩
  have hT : ∀ v, T.app v = v + ((B z y)⁻¹ * B v y) • y :=
    fun v => symplecticTransvection_apply hB y _ v
  have h1 : T.app x = x := by rw [hT, hxy, mul_zero, zero_smul, add_zero]
  have h2 : T.app z = z + y := by rw [hT, inv_mul_cancel₀ hz, one_smul]
  have h3 := hg T h1 z
  rw [h2, map_add] at h3
  simpa using h3

theorem biadd_eq_zero_of_form_eq_zero {A : Type*} [AddCommGroup A] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) (f : V →+ V →+ A)
    (hf : ∀ (g : Gsp B) (x y : V), f (g.app x) (g.app y) = f x y) {x y : V} (hxy : B x y = 0) :
    f x y = 0 :=
  additive_eq_zero_of_form_eq_zero hB hBn (f x)
    (fun T hT z => by
      have h := hf T x z
      rwa [hT] at h) hxy

end Abstract

section Matrix

variable {m : ℕ} {K : Type} [Field K]

theorem additive_eq_zero_of_range_spForm {Y : Type*} [Group Y] {A : Type*} [AddGroup A]
    (φ : Y →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K)
    (g : (Fin m ⊕ Fin m → K) →+ A) {x : Fin m ⊕ Fin m → K}
    (hg : ∀ (y : Y), (φ y).val *ᵥ x = x → ∀ z : Fin m ⊕ Fin m → K,
      g ((φ y).val *ᵥ z) = g z) {y' : Fin m ⊕ Fin m → K} (hxy : spForm m K x y' = 0) :
    g y' = 0 := by
  refine additive_eq_zero_of_form_eq_zero spForm_isAlt spForm_nondegenerate g
    (fun T hT z => ?_) hxy
  have ha : ∀ v, T.app v = ((spEquiv (m := m) (K := K)).symm T : GL (Fin m ⊕ Fin m) K).val *ᵥ v :=
    fun v => by
      have := spEquiv_app ((spEquiv (m := m) (K := K)).symm T) v
      rw [MulEquiv.apply_symm_apply] at this
      exact this
  have hmem : ((spEquiv (m := m) (K := K)).symm T : GL (Fin m ⊕ Fin m) K) ∈ φ.range := by
    rw [hφ]
    exact ((spEquiv (m := m) (K := K)).symm T).2
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
  rw [ha z]
  rw [ha x] at hT
  rw [← hy] at hT ⊢
  exact hg y hT z

theorem biadd_eq_zero_of_spForm_eq_zero {A : Type*} [AddCommGroup A]
    (f : (Fin m ⊕ Fin m → K) →+ (Fin m ⊕ Fin m → K) →+ A)
    (hf : ∀ g ∈ StatedSp m K, ∀ x y : Fin m ⊕ Fin m → K,
      f ((g : GL (Fin m ⊕ Fin m) K).val *ᵥ x) ((g : GL (Fin m ⊕ Fin m) K).val *ᵥ y) = f x y)
    {x y : Fin m ⊕ Fin m → K} (hxy : spForm m K x y = 0) : f x y = 0 := by
  refine biadd_eq_zero_of_form_eq_zero spForm_isAlt spForm_nondegenerate f (fun g a b => ?_) hxy
  have ha : ∀ v, g.app v = ((spEquiv (m := m) (K := K)).symm g : GL (Fin m ⊕ Fin m) K).val *ᵥ v :=
    fun v => by
      have := spEquiv_app ((spEquiv (m := m) (K := K)).symm g) v
      rw [MulEquiv.apply_symm_apply] at this
      exact this
  rw [ha a, ha b]
  exact hf _ ((spEquiv (m := m) (K := K)).symm g).2 a b

end Matrix

end CFSG.ClassicalGroups.Symplectic
